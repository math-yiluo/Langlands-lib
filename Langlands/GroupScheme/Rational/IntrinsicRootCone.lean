import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots

/-! # Intrinsic positive roots lie in the nonnegative restricted-root cone

For a verified parabolic root presentation whose ambient relative roots are closed
under negation, the real vector of every intrinsic positive split-component root is a
nonnegative combination of the restricted simple roots.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- The restriction of a positive ambient relative root to the split component has its
real vector in the nonnegative cone: selected simple roots restrict to zero, the other
simple roots restrict to restricted simple roots, and the cone is closed under sums. -/
theorem one_tmul_restrict_mem_nonnegCone
    {α : characterLattice r.data.T}
    (hα : α ∈ positiveRelativeRoots r.data.i r.data.ν) :
    (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ α) ∈ r.nonnegCone := by
  refine positiveRelativeRoots_induction r.data.i r.data.ν
    (P := fun χ => (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ χ) ∈ r.nonnegCone) ?_ ?_ hα
  · intro χ hχ
    by_cases hJ : χ ∈ r.data.J
    · simp only [r.selectedRoot_restrict_eq_zero hJ, tmul_zero]
      exact r.zero_mem_nonnegCone
    · exact RootCombination.subset_nonneg _
        (r.mem_restrictedRoots.mpr ⟨χ, hχ, hJ, rfl⟩)
  · intro χ _ ψ _ hχ hψ
    simp only [Preadditive.comp_add, tmul_add]
    exact r.add_mem_nonnegCone hχ hψ

/-- Renard's cone of a represented parabolic contains every intrinsic positive root of
its split component, once the ambient relative roots are closed under negation. -/
theorem one_tmul_mem_nonnegCone_of_mem_intrinsicPositiveRoots
    (hneg : ∀ α ∈ relativeRoots r.data.i, -α ∈ relativeRoots r.data.i)
    {β : characterLattice A} (hβ : β ∈ r.intrinsicPositiveRoots) :
    (1 : ℝ) ⊗ₜ[ℤ] β ∈ r.nonnegCone := by
  obtain ⟨α, hα, rfl⟩ := r.exists_positiveRoot_restrict hneg hβ
  exact r.one_tmul_restrict_mem_nonnegCone hα

end Langlands.GroupScheme.ParabolicRootPresentation
