import Langlands.Geometry.Building.AffineRootSystem
import Mathlib.Data.Set.Card

/-! # A finite root count decreasing along strict affine face incidence -/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

open scoped Affine

universe uV uA

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The derivative determines an affine functional that vanishes at a given point. -/
theorem linear_injOn_vanishingRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    Set.InjOn (fun ψ : A →ᵃ[ℝ] ℝ => ψ.linear) (vanishingRoots Ψ x) := by
  intro ψ hψ η hη hlin
  exact AffineMap.ext_linear hlin (hψ.2.trans hη.2.symm)

/-- Finitely many root derivatives give finitely many roots vanishing at any point. -/
theorem finite_vanishingRoots (hΨ : (derivativeRoots Ψ).Finite) (x : A) :
    (vanishingRoots Ψ x).Finite :=
  Set.Finite.of_injOn (fun _ hψ => linear_mem_derivativeRoots hψ.1)
    (linear_injOn_vanishingRoots Ψ x) hΨ

/-- The number of affine roots vanishing at a point. This is a root count,
not the codimension of its facet. -/
def vanishingRootCount (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : ℕ :=
  (vanishingRoots Ψ x).ncard

theorem vanishingRootCount_eq_of_facetRel {x y : A} (h : facetRel Ψ x y) :
    vanishingRootCount Ψ x = vanishingRootCount Ψ y :=
  congrArg Set.ncard (vanishingRoots_eq_of_facetRel h)

/-- Passing to a face can only add vanishing roots. -/
theorem vanishingRoots_subset_of_mem_facetClosure {x y : A}
    (hxy : x ∈ facetClosure Ψ y) : vanishingRoots Ψ y ⊆ vanishingRoots Ψ x := by
  intro ψ hψ
  refine ⟨hψ.1, sign_eq_zero_iff.mp ?_⟩
  rcases hxy ψ hψ.1 with h | h
  · exact h
  · exact h.trans (sign_eq_zero_iff.mpr hψ.2)

/-- Equal vanishing-root sets at incident points force equality of all root signs. -/
theorem facetRel_of_mem_facetClosure_of_vanishingRoots_subset {x y : A}
    (hxy : x ∈ facetClosure Ψ y)
    (hsub : vanishingRoots Ψ x ⊆ vanishingRoots Ψ y) : facetRel Ψ x y := by
  intro ψ hψ
  rcases hxy ψ hψ with h | h
  · have hy : ψ y = 0 := (hsub ⟨hψ, sign_eq_zero_iff.mp h⟩).2
    exact h.trans (sign_eq_zero_iff.mpr hy).symm
  · exact h

/-- A strict face has strictly more vanishing roots than its upper facet. -/
theorem vanishingRoots_ssubset_of_mem_facetClosure {x y : A}
    (hxy : x ∈ facetClosure Ψ y) (hne : ¬ facetRel Ψ x y) :
    vanishingRoots Ψ y ⊂ vanishingRoots Ψ x := by
  refine ⟨vanishingRoots_subset_of_mem_facetClosure hxy, ?_⟩
  intro hsub
  exact hne (facetRel_of_mem_facetClosure_of_vanishingRoots_subset hxy hsub)

theorem vanishingRootCount_le_of_mem_facetClosure
    (hΨ : (derivativeRoots Ψ).Finite) {x y : A}
    (hxy : x ∈ facetClosure Ψ y) :
    vanishingRootCount Ψ y ≤ vanishingRootCount Ψ x :=
  Set.ncard_le_ncard (vanishingRoots_subset_of_mem_facetClosure hxy)
    (finite_vanishingRoots hΨ x)

theorem vanishingRootCount_lt_of_mem_facetClosure
    (hΨ : (derivativeRoots Ψ).Finite) {x y : A}
    (hxy : x ∈ facetClosure Ψ y) (hne : ¬ facetRel Ψ x y) :
    vanishingRootCount Ψ y < vanishingRootCount Ψ x :=
  Set.ncard_lt_ncard (vanishingRoots_ssubset_of_mem_facetClosure hxy hne)
    (finite_vanishingRoots hΨ x)

/-- Precomposition by a root-preserving affine automorphism bijects the
vanishing-root sets at corresponding points. -/
theorem image_comp_vanishingRoots {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) (x : A) :
    (fun ψ : A →ᵃ[ℝ] ℝ => ψ.comp (e : A →ᵃ[ℝ] A)) ''
      vanishingRoots Ψ (e x) = vanishingRoots Ψ x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨ψ, hψ, rfl⟩
    exact (mem_vanishingRoots_apply he x ψ).mp hψ
  · intro ψ hψ
    refine ⟨ψ.comp ((e⁻¹ : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A), ?_, comp_inv_comp e ψ⟩
    apply (mem_vanishingRoots_apply he x _).mpr
    simpa only [comp_inv_comp] using hψ

/-- The root count is invariant under every actual root-preserving affine
coordinate change, without any finiteness premise. -/
theorem vanishingRootCount_apply {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) (x : A) :
    vanishingRootCount Ψ (e x) = vanishingRootCount Ψ x := by
  have hinj : Function.Injective
      (fun ψ : A →ᵃ[ℝ] ℝ => ψ.comp (e : A →ᵃ[ℝ] A)) := by
    intro ψ η h
    apply AffineMap.ext
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    exact DFunLike.congr_fun h w
  exact (hinj.injOn.ncard_image).symm.trans
    (congrArg Set.ncard (image_comp_vanishingRoots he x))

/-- A finite, facet-constant root count that is invariant under chart changes
and strictly decreases in the upward direction of strict face incidence. -/
def AffineFacetRootCountStatement (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Prop :=
  (derivativeRoots Ψ).Finite →
    (∀ x : A, (vanishingRoots Ψ x).Finite) ∧
    (∀ x y : A, facetRel Ψ x y → vanishingRootCount Ψ x = vanishingRootCount Ψ y) ∧
    (∀ (e : A ≃ᵃ[ℝ] A), e ∈ rootStabilizer Ψ →
      ∀ x : A, vanishingRootCount Ψ (e x) = vanishingRootCount Ψ x) ∧
    (∀ x y : A, x ∈ facetClosure Ψ y → ¬ facetRel Ψ x y →
      vanishingRootCount Ψ y < vanishingRootCount Ψ x)

theorem affineFacetRootCount (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    AffineFacetRootCountStatement Ψ := by
  intro hΨ
  exact ⟨finite_vanishingRoots hΨ,
    fun _ _ h => vanishingRootCount_eq_of_facetRel h,
    fun _ he => vanishingRootCount_apply he,
    fun _ _ hxy hne => vanishingRootCount_lt_of_mem_facetClosure hΨ hxy hne⟩

end Langlands.Geometry.Building.AffineRootSystem
