{-# OPTIONS --cubical #-}

module E1 where

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties


open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
-- open import Cubical.Data.Prod
open import Cubical.Data.Maybe

open import Cubical.Data.Empty

open import Cubical.Data.Sum

open import Cubical.Data.List as L


open import Agda.Builtin.String

open import Cubical.Data.Graph

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.SetQuotients

open import StateType

module Example₁ where


  record HttpObj : Type₀ where

    constructor http
    field
      reqCount : ℕ

  open HttpObj

  reqCountInj : ∀ x y → reqCount x ≡ reqCount y → x ≡ y
  reqCountInj x y x₁ i = http (x₁ i)

  HttpObjDisc : Discrete HttpObj
  HttpObjDisc x y =
     mapDec (λ x₁ i → reqCountInj x y x₁ i)
            (λ x₁ x₂ → x₁ (cong reqCount x₂))
            (discreteℕ (reqCount x) (reqCount y))



  data HttpHom : HttpObj → HttpObj → Type₀ where  
    reg : ∀ k → HttpHom (http k) (http (suc k))  


  Http : StateType 
  Http = record
       { Obj = HttpObj
       ; obj₀ = http zero
       ; _O≟_ = HttpObjDisc 
       ; Hom = HttpHom
       ; _H≟_ = {!!}
       }



  data FieldObj : Type₀ where
    edClean : ℕ → FieldObj
    edDirty : ℕ → ℕ → FieldObj

  commitedVal : FieldObj → ℕ
  commitedVal (edClean x) = x
  commitedVal (edDirty x x₁) = x

  data FieldHom : FieldObj → FieldObj → Type₀ where  
    edEdit : ∀ x n → FieldHom x (edDirty (commitedVal x) n)
    edSave : ∀ n' n → FieldHom (edDirty n' n) (edClean n)
    edDiscard : ∀ n' n → FieldHom (edDirty n' n) (edClean n')


  Field : StateType
  Field = record
        { Obj = FieldObj
        ; obj₀ = edClean 0
        ; _O≟_ = {!!}
        ; Hom = FieldHom
        ; _H≟_ = {!!}
        }



-- --- Example


-- Http : Graph ℓ-zero ℓ-zero
-- Http = record { Obj = HttpObj ; Hom = HttpHom }
--    where

--    data HttpObj : Type₀ where
     
--    data HttpHom : HttpObj → HttpObj → Type₀ where  


-- -- data EntityData (e : Entity) : Type₀ where
-- --   edClean : ℕ → EntityData e 
-- --   edDirty : ℕ → EntityData e 
-- --   edEdit : ∀ x n → x ≡ edDirty n
-- --   edSave : ∀ n → edDirty n ≡ edClean n

-- G-Paths : ∀ {ℓ ℓ'} → (G : Graph ℓ ℓ') → Type (ℓ-max ℓ ℓ')  
-- G-Paths G = Graph.Obj G / Graph.Hom G

-- MainS : Graph ℓ-zero ℓ-zero
-- MainS = record { Obj = MainSObj ; Hom = MainSHom }
--    where

--    data MainSObj : Type₀ where
--      noEntitySelected : MainSObj
--      entitySelected : Entity → MainSObj

--    data MainSHom : MainSObj → MainSObj → Type₀ where  
--      selectEntity : ∀ e → MainSHom noEntitySelected (entitySelected e)
--      deSelectEntity : ∀ e → MainSHom  (entitySelected e) noEntitySelected

-- EntityS : Entity → Graph ℓ-zero ℓ-zero
-- EntityS e = record { Obj = EntitySObj e ; Hom = EntitySHom e }
--    where

--    data EntitySObj (e : Entity) : Type₀ where
--      edClean : ℕ → EntitySObj e
--      edDirty : ℕ → ℕ → EntitySObj e

--    commitedVal : ∀ {e} → EntitySObj e → ℕ
--    commitedVal (edClean x) = x
--    commitedVal (edDirty x x₁) = x

--    data EntitySHom (e : Entity) : EntitySObj e → EntitySObj e → Type₀ where  
--      edEdit : ∀ x n → EntitySHom e x (edDirty (commitedVal x) n)
--      edSave : ∀ n' n → EntitySHom e (edDirty n' n) (edClean n)
--      edDiscard : ∀ n' n → EntitySHom e (edDirty n' n) (edClean n')
