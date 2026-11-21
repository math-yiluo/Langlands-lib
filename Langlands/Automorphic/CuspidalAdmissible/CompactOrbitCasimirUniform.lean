import Langlands.Automorphic.CuspidalAdmissible.CompactCasimirAnnihilator
import Langlands.Representation.FiniteVectors

/-! Uniform compact Casimir annihilation on the equivariant images of an orbit. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalAdmissible

open Global FiniteVectors Polynomial

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)
  {V : Type*} [AddCommGroup V] [Module ℂ V]

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

/-- One polynomial kills the compact Casimir on all equivariant images
of a given vector under compact intertwiners. -/
def CompactCasimirKillsEquivariantImages
    (ρ : Representation ℂ (standardInfiniteCompact F n) V) (v : V) (p : ℂ[X]) : Prop :=
  ∀ f : V →ₗ[ℂ] S.Space, (∀ k x, f (ρ k x) = S.compactRepresentation k (f x)) →
    aeval (compactCasimirOperator S) p (f v) = 0

/-- Every compact-finite vector admits a common compact Casimir annihilator
for all of its equivariant images in a fixed actual realization. -/
theorem exists_compactCasimir_annihilator_of_finiteVector
    (ρ : Representation ℂ (standardInfiniteCompact F n) V) (v : V)
    (hv : IsFiniteVector ρ v) :
    ∃ p : ℂ[X], p ≠ 0 ∧ CompactCasimirKillsEquivariantImages S ρ v p := by
  let Z := orbitSubrepresentation ρ v
  have : Module.Finite ℂ Z.toSubmodule := hv
  let e := (Module.finBasis ℂ Z.toSubmodule).equivFun
  let σ : Representation ℂ (standardInfiniteCompact F n)
      (Fin (Module.finrank ℂ Z.toSubmodule) → ℂ) :=
    (MonoidHomClass.toMonoidHom (e.conjAlgEquiv ℂ)).comp Z.toRepresentation
  obtain ⟨p, hp, hann⟩ := exists_compactCasimir_annihilator S σ
  refine ⟨p, hp, fun f hf => ?_⟩
  let g := f ∘ₗ Z.toSubmodule.subtype ∘ₗ e.symm.toLinearMap
  have hg (k : standardInfiniteCompact F n) (x : Fin (Module.finrank ℂ Z.toSubmodule) → ℂ) :
      g (σ k x) = S.compactRepresentation k (g x) := by
    change f (e.symm (e (Z.toRepresentation k (e.symm x)))).val =
      S.compactRepresentation k (f (e.symm x).val)
    rw [e.symm_apply_apply]
    exact hf k (e.symm x).val
  have h := hann g hg (e ⟨v, self_mem_orbitSpan ρ v⟩)
  simpa only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Submodule.subtype_apply] using h

/-- Restricting a compact-finite vector along a homomorphism into its
acting group preserves the uniform annihilator conclusion. -/
theorem exists_compactCasimir_annihilator_of_finiteVector_comp
    {G : Type*} [Monoid G] (ρ : Representation ℂ G V)
    (α : standardInfiniteCompact F n →* G) (v : V) (hv : IsFiniteVector ρ v) :
    ∃ p : ℂ[X], p ≠ 0 ∧ CompactCasimirKillsEquivariantImages S (ρ.comp α) v p := by
  apply exists_compactCasimir_annihilator_of_finiteVector
  have : Module.Finite ℂ (orbitSpan ρ v) := hv
  have h : orbitSpan (ρ.comp α) v ≤ orbitSpan ρ v := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact action_mem_orbitSpan ρ (α k) v
  exact Submodule.finiteDimensional_of_le h

end Langlands.Automorphic.CuspidalAdmissible
