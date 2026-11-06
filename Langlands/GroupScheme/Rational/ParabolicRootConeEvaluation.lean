import Langlands.GroupScheme.Rational.ParabolicRootPresentationIntrinsicRoots

/-! # Evaluation of root cones on a defining split-component cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- Evaluation of a real split-component character on the defining integral
cocharacter chosen by the compatible presentation. -/
def splitComponentEvaluation : Vstar A →ₗ[ℝ] ℝ :=
  (pair A).flip ((1 : ℝ) ⊗ₜ[ℤ] r.splitComponentCocharacter)

@[simp]
theorem splitComponentEvaluation_tmul (s : ℝ) (χ : characterLattice A) :
    r.splitComponentEvaluation (s ⊗ₜ[ℤ] χ) =
      s * (latticePairing A χ r.splitComponentCocharacter : ℝ) := by
  simp [splitComponentEvaluation]

/-- Every restricted simple root has positive evaluation, without an
independence or relative-root-system hypothesis. -/
theorem splitComponentEvaluation_pos_of_mem_restrictedRoots
    {β : Vstar A} (hβ : β ∈ r.restrictedRoots) :
    0 < r.splitComponentEvaluation β := by
  obtain ⟨α, hα, hαJ, rfl⟩ := r.mem_restrictedRoots.mp hβ
  rw [splitComponentEvaluation_tmul, one_mul]
  exact_mod_cast (r.restrict_mem_intrinsicPositiveRoots hα hαJ).2

variable [LocallyOfFiniteType G.X.hom]

/-- The defining evaluation is nonnegative on the entire nonnegative cone. -/
theorem splitComponentEvaluation_nonneg_of_mem_nonnegCone
    {x : Vstar A} (hx : x ∈ r.nonnegCone) :
    0 ≤ r.splitComponentEvaluation x := by
  obtain ⟨c, hc, rfl⟩ :=
    (RootCombination.mem_nonneg r.finite_restrictedRoots).mp hx
  rw [map_sum]
  apply Finset.sum_nonneg
  intro β hβ
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg (hc β (r.finite_restrictedRoots.mem_toFinset.mp hβ))
    (r.splitComponentEvaluation_pos_of_mem_restrictedRoots
      (r.finite_restrictedRoots.mem_toFinset.mp hβ)).le

/-- A positive combination has positive evaluation if the restricted-root
set is nonempty. -/
theorem splitComponentEvaluation_pos_of_mem_positiveCone
    (hne : r.restrictedRoots.Nonempty) {x : Vstar A}
    (hx : x ∈ r.positiveCone) : 0 < r.splitComponentEvaluation x := by
  obtain ⟨c, hc, rfl⟩ :=
    (RootCombination.mem_positive r.finite_restrictedRoots).mp hx
  rw [map_sum]
  apply Finset.sum_pos
  · intro β hβ
    rw [map_smul, smul_eq_mul]
    exact mul_pos (hc β (r.finite_restrictedRoots.mem_toFinset.mp hβ))
      (r.splitComponentEvaluation_pos_of_mem_restrictedRoots
        (r.finite_restrictedRoots.mem_toFinset.mp hβ))
  · obtain ⟨β, hβ⟩ := hne
    exact ⟨β, r.finite_restrictedRoots.mem_toFinset.mpr hβ⟩

/-- The positive cone contains zero exactly in the empty-root case. -/
theorem zero_mem_positiveCone_iff_restrictedRoots_eq_empty :
    (0 : Vstar A) ∈ r.positiveCone ↔ r.restrictedRoots = ∅ := by
  constructor
  · intro hzero
    by_contra hne
    have hpos := r.splitComponentEvaluation_pos_of_mem_positiveCone
      (Set.nonempty_iff_ne_empty.mpr hne) hzero
    simp only [map_zero, lt_self_iff_false] at hpos
  · intro hempty
    have hsubset := r.restrictedRoots_eq_empty_iff.mp hempty
    rw [r.positiveCone_of_eq_empty (Set.sdiff_eq_empty.mpr hsubset)]
    exact Set.mem_singleton 0

/-- The same criterion expressed using the ambient simple-root index. -/
theorem zero_mem_positiveCone_iff_simpleRoots_subset :
    (0 : Vstar A) ∈ r.positiveCone ↔
      simpleRelativeRoots r.data.i r.data.ν ⊆ r.data.J :=
  r.zero_mem_positiveCone_iff_restrictedRoots_eq_empty.trans
    r.restrictedRoots_eq_empty_iff

end Langlands.GroupScheme.ParabolicRootPresentation
