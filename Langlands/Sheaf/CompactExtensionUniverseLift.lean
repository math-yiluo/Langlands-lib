import Langlands.Sheaf.HomeomorphTransport
import Langlands.Sheaf.CompactSoft

/-! # Compact extensions and ordinary c-softness after universe lift -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.CompactExtension

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Sheaf.CompactSoft

universe v w

variable {X : Type v} [TopologicalSpace X]

/-- The open complement of the closure of an open. -/
def outsideClosure (V : Opens X) : Opens X :=
  ⟨(closure (V : Set X))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Sections near compact sets extend on a smaller neighborhood to global
sections vanishing outside the compact closure of that neighborhood. This
formulation does not tie the space and coefficient universes. -/
def HasCompactExtensions {S : Type w} [CommRing S]
    (F : TopCat.Sheaf (ModuleCat.{w} S) (TopCat.of X)) : Prop :=
  ∀ (C : Set X), IsCompact C → ∀ (U : Opens X), C ⊆ U →
    ∀ s : F.obj.obj (op U), ∃ (V : Opens X) (i : V ⟶ U)
      (t : F.obj.obj (op ⊤)),
      C ⊆ V ∧ IsCompact (closure (V : Set X)) ∧
        F.obj.map (homOfLE le_top : V ⟶ ⊤).op t = F.obj.map i.op s ∧
        F.obj.map (homOfLE le_top : outsideClosure V ⟶ ⊤).op t = 0

variable {R : Type (max v w)} [CommRing R]
variable (F : TopCat.Sheaf (ModuleCat.{max v w} R) (TopCat.of X))

/-- The same actual sheaf transported to a space in the coefficient universe. -/
def universeLift :
    TopCat.Sheaf (ModuleCat.{max v w} R) (TopCat.of (ULift.{max v w} X)) :=
  (HomeomorphTransport.equivalence
    (Homeomorph.ulift.{max v w, v} (X := X)).symm (ModuleCat.{max v w} R)).functor.obj F

/-- Compact extension on the original space gives the existing native
c-softness predicate on its actual universe-lifted sheaf. -/
theorem isCSoft_universeLift (hF : HasCompactExtensions F) :
    IsCSoft (universeLift F) := by
  let e : ULift.{max v w} X ≃ₜ X := Homeomorph.ulift
  let a := HomeomorphTransport.opensEquivalence e.symm
  let T := universeLift F
  change IsCSoft T
  rw [isCSoft_iff]
  intro C hC z
  obtain ⟨U, hCU, s, rfl⟩ := exists_setGerm_eq T.obj z
  let U₀ : Opens X := a.inverse.obj U
  have hC₀ : IsCompact (e '' C) := hC.image e.continuous
  have hCU₀ : e '' C ⊆ U₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hCU hx
  obtain ⟨V, i, t, hCV, hVc, ht, hzero⟩ := hF (e '' C) hC₀ U₀ hCU₀ s
  let V' : Opens (ULift.{max v w} X) := a.functor.obj V
  let W' : Opens (ULift.{max v w} X) := a.functor.obj (outsideClosure V)
  have hCV' : C ⊆ V' := by
    intro x hx
    exact hCV ⟨x, hx, rfl⟩
  have hV'U : V' ≤ U := by
    intro x hx
    exact i.le hx
  let t' : T.obj.obj (op ⊤) := t
  have hz : T.obj.map (homOfLE le_top : W' ⟶ ⊤).op t' = 0 := by
    exact hzero
  refine ⟨t', ?_, ?_⟩
  · refine ((e.isCompact_preimage).2 hVc).of_isClosed_subset
      (Langlands.Sheaf.CompactSupport.isClosed_support _ _) ?_
    intro x hx
    by_contra hxV
    have hxW : x ∈ W' := hxV
    apply hx
    change T.presheaf.Γgerm x t' = 0
    rw [← T.presheaf.Γgerm_res_apply (U := W') x hxW t' (i := homOfLE le_top),
      hz, map_zero]
  · refine setGerm_ext T.obj _ _ hCV'
      (homOfLE le_top : V' ⟶ ⊤) (homOfLE hV'U : V' ⟶ U) ?_
    exact ht

end Langlands.Sheaf.CompactExtension
