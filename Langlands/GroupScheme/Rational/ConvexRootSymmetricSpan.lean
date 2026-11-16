import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.LinearAlgebra.RationalRealSpan

/-! # Saturation of the symmetric part of a convex root subset -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The rational character span of the symmetric part of a root subset. -/
def symmetricRootRatSpan (X : Set (characterLattice T)) :
    Submodule ℚ (ℚ ⊗[ℤ] characterLattice T) :=
  ratSpan (parabolicRootLevi X)

/-- The real span of the symmetric roots of a convex subset lies in the
lineality space of its defining cone. -/
theorem IsConvexRootSubset.mem_parabolicRootLevi_of_mem_realSpan
    {R X : Set (characterLattice T)} (hX : IsConvexRootSubset R X)
    (hneg : ∀ γ ∈ R, -γ ∈ R) {γ : characterLattice T} (hγ : γ ∈ R)
    (hspan : (1 : ℝ) ⊗ₜ[ℤ] γ ∈
      Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) ''
        parabolicRootLevi X)) :
    γ ∈ parabolicRootLevi X := by
  obtain ⟨C, -, hC⟩ := hX
  have hle : Submodule.span ℝ
      ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' parabolicRootLevi X) ≤
      C.lineal := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    have hp := (Set.ext_iff.mp hC α).mp hα.1
    have hn := (Set.ext_iff.mp hC (-α)).mp hα.2
    exact PointedCone.mem_lineal.mpr
      ⟨hp.2, by simpa only [TensorProduct.tmul_neg] using hn.2⟩
  have hc := PointedCone.mem_lineal.mp (hle hspan)
  exact ⟨(Set.ext_iff.mp hC γ).mpr ⟨hγ, hc.1⟩,
    (Set.ext_iff.mp hC (-γ)).mpr ⟨hneg γ hγ,
      by simpa only [TensorProduct.tmul_neg] using hc.2⟩⟩

/-- Among ambient roots, the symmetric part of a convex subset is saturated
in its rational character span. -/
theorem IsConvexRootSubset.mem_symmetricRootRatSpan_iff
    {R X : Set (characterLattice T)} (hX : IsConvexRootSubset R X)
    (hneg : ∀ γ ∈ R, -γ ∈ R) {γ : characterLattice T} (hγ : γ ∈ R) :
    toRat γ ∈ symmetricRootRatSpan X ↔ γ ∈ parabolicRootLevi X := by
  constructor
  · intro h
    apply hX.mem_parabolicRootLevi_of_mem_realSpan hneg hγ
    rw [← toReal_toRat (characterLattice T) γ]
    exact (toReal_mem_span_iff (characterLattice T) (parabolicRootLevi X) (toRat γ)).mpr h
  · intro h
    exact Submodule.subset_span ⟨γ, h, rfl⟩

/-- The ambient roots in the symmetric rational span are exactly the
symmetric part of the convex subset. -/
theorem IsConvexRootSubset.parabolicRootLevi_eq_roots_in_symmetricRootRatSpan
    {R X : Set (characterLattice T)} (hX : IsConvexRootSubset R X)
    (hneg : ∀ γ ∈ R, -γ ∈ R) :
    parabolicRootLevi X = {γ | γ ∈ R ∧ toRat γ ∈ symmetricRootRatSpan X} := by
  ext γ
  constructor
  · intro h
    have hγ := hX.isClosedRootSubset.1 h.1
    exact ⟨hγ, (hX.mem_symmetricRootRatSpan_iff hneg hγ).mpr h⟩
  · rintro ⟨hγ, hspan⟩
    exact (hX.mem_symmetricRootRatSpan_iff hneg hγ).mp hspan

end Langlands.GroupScheme
