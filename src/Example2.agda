{-# OPTIONS --cubical #-}

module Example2 where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod
open import Cubical.Data.Maybe
open import Cubical.Data.Empty

open import Cubical.Data.Sum

open import Cubical.Data.List as L


open import Agda.Builtin.String

open import Cubical.Data.Graph

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.SetQuotients


data Entity : Type₀ where
  e1 e2 e3 : Entity




-- data Cmd : Type₀ where
--   reqGet : Entity → Cmd
--   respGet : ℕ → Cmd
--   regSet : Entity → ℕ → Cmd
--   respSet : Bool → Cmd

Http : Graph ℓ-zero ℓ-zero
Http = record { Obj = HttpObj ; Hom = HttpHom }
   where

   data HttpObj : Type₀ where
     
   data HttpHom : HttpObj → HttpObj → Type₀ where  


-- data EntityData (e : Entity) : Type₀ where
--   edClean : ℕ → EntityData e 
--   edDirty : ℕ → EntityData e 
--   edEdit : ∀ x n → x ≡ edDirty n
--   edSave : ∀ n → edDirty n ≡ edClean n

G-Paths : ∀ {ℓ ℓ'} → (G : Graph ℓ ℓ') → Type (ℓ-max ℓ ℓ')  
G-Paths G = Graph.Obj G / Graph.Hom G

MainS : Graph ℓ-zero ℓ-zero
MainS = record { Obj = MainSObj ; Hom = MainSHom }
   where

   data MainSObj : Type₀ where
     noEntitySelected : MainSObj
     entitySelected : Entity → MainSObj

   data MainSHom : MainSObj → MainSObj → Type₀ where  
     selectEntity : ∀ e → MainSHom noEntitySelected (entitySelected e)
     deSelectEntity : ∀ e → MainSHom  (entitySelected e) noEntitySelected

EntityS : Entity → Graph ℓ-zero ℓ-zero
EntityS e = record { Obj = EntitySObj e ; Hom = EntitySHom e }
   where

   data EntitySObj (e : Entity) : Type₀ where
     edClean : ℕ → EntitySObj e
     edDirty : ℕ → ℕ → EntitySObj e

   commitedVal : ∀ {e} → EntitySObj e → ℕ
   commitedVal (edClean x) = x
   commitedVal (edDirty x x₁) = x

   data EntitySHom (e : Entity) : EntitySObj e → EntitySObj e → Type₀ where  
     edEdit : ∀ x n → EntitySHom e x (edDirty (commitedVal x) n)
     edSave : ∀ n' n → EntitySHom e (edDirty n' n) (edClean n)
     edDiscard : ∀ n' n → EntitySHom e (edDirty n' n) (edClean n')




MaybeGraph : (G : Graph ℓ-zero ℓ-zero) → (Graph.Obj G → Bool) →  (Graph.Obj G → Bool) → Graph ℓ-zero ℓ-zero 
MaybeGraph G isEntryState isExitState =
  record { Obj = Maybe (Graph.Obj G) ; Hom = hom }

  where
    hom : Maybe (Obj G) → Maybe (Obj G) → Type ℓ-zero
    hom nothing nothing = Unit
    hom nothing (just x) = if (isEntryState x) then Unit else ⊥
    hom (just x) nothing = if (isExitState x) then Unit else ⊥
    hom (just x) (just x₁) = Graph.Hom G x x₁
    



BiGraph : (G₁ G₂ : Graph ℓ-zero ℓ-zero)
            → (  (o₁ o₁' : Graph.Obj G₁)
               → (o₂ o₂' : Graph.Obj G₂)
               → Graph.Hom G₁ o₁ o₁'
               → Graph.Hom G₂ o₂ o₂'
               → Maybe Bool)
            → Graph ℓ-zero ℓ-zero
BiGraph G₁ G₂ f =
  record { Obj = o ; Hom = h }
  where
   open Graph

   o : Type ℓ-zero
   o = Obj G₁ × Obj G₂


   h : o → o → Type ℓ-zero
   h (o₁ , o₂) (o₁' , o₂') =
     let f' = f o₁ o₁'  o₂ o₂'
     in Σ {!!} {!!}
     
-- record Component : Type₁ where

--   open Graph

--   field
--     state : Graph ℓ-zero ℓ-zero
--     msg : Obj state → Type₀
--     ctrl : (s : Obj state) → msg s → Σ (Obj state) (λ x → (_/_.[_] {R = Hom state} s) ≡ _/_.[ x ] ) × Cmd

-- componentFromGraph : Graph ℓ-zero ℓ-zero → Component
-- Component.state (componentFromGraph x) = x
-- Component.msg (componentFromGraph x) y = Σ _ (Hom x y)
-- Component.ctrl (componentFromGraph x) s x₁ = (fst x₁ , eq/ s (fst x₁) (snd x₁)) , noOp
