import Langlands.GroupScheme.Torus.FundamentalWeightPermutation
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # The sum of the three fundamental leaf weights of D4 -/

noncomputable section

namespace Langlands.RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (e : b.support ≃ Fin 4)

/-- The sum of the fundamental weights at the three leaves of a D4 numbering.
The central vertex in Mathlib's numbering is `1`. -/
def d4LeafWeightSum : X :=
  fundamentalWeightBasis P b hspan (e.symm 0) +
    fundamentalWeightBasis P b hspan (e.symm 2) +
    fundamentalWeightBasis P b hspan (e.symm 3)

/-- The three fundamental leaf weights sum to an integral combination of roots. -/
theorem d4LeafWeightSum_eq
    (hD : ∀ i j : b.support, P.pairing i j = CartanMatrix.D 4 (e i) (e j)) :
    d4LeafWeightSum P b hspan e =
      (2 : ℤ) • P.root (e.symm 0) + (3 : ℤ) • P.root (e.symm 1) +
        (2 : ℤ) • P.root (e.symm 2) + (2 : ℤ) • P.root (e.symm 3) := by
  classical
  apply Langlands.RootDatumSimpleCorootEquiv.eq_of_pairing_simpleCoroot b hspan
  intro j
  obtain ⟨i, rfl⟩ := e.symm.surjective j
  fin_cases i <;>
    simp [d4LeafWeightSum, map_add, fundamentalWeightBasis_pairing,
      P.root_coroot_eq_pairing, hD, CartanMatrix.D]

/-- Consequently the leaf-weight sum vanishes modulo the integral root lattice. -/
theorem d4LeafWeightSum_mem_rootSpan
    (hD : ∀ i j : b.support, P.pairing i j = CartanMatrix.D 4 (e i) (e j)) :
    d4LeafWeightSum P b hspan e ∈ P.rootSpan ℤ := by
  rw [d4LeafWeightSum_eq P b hspan e hD]
  exact add_mem
    (add_mem
      (add_mem
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))

/-- The classes of the three leaf weights sum to zero in the actual lattice quotient. -/
theorem d4LeafWeight_classes_sum_eq_zero
    (hD : ∀ i j : b.support, P.pairing i j = CartanMatrix.D 4 (e i) (e j)) :
    (P.rootSpan ℤ).mkQ (fundamentalWeightBasis P b hspan (e.symm 0)) +
      (P.rootSpan ℤ).mkQ (fundamentalWeightBasis P b hspan (e.symm 2)) +
      (P.rootSpan ℤ).mkQ (fundamentalWeightBasis P b hspan (e.symm 3)) = 0 := by
  rw [← map_add, ← map_add]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (d4LeafWeightSum_mem_rootSpan P b hspan e hD)

end Langlands.RootDatum
