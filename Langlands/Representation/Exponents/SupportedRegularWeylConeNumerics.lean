import Langlands.Representation.Exponents.Chambers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite-coordinate helpers for the supported regular Weyl comparison. -/

noncomputable section

namespace Langlands.SupportedRegularWeylComparison

open Exponents Finset
open scoped BigOperators

set_option autoImplicit false

private def coordinateExtend {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then x ⟨k, hk⟩ else 0

private theorem coordinateExtend_lt {n : ℕ} (x : Fin n → ℝ)
    {k : ℕ} (hk : k < n) : coordinateExtend x k = x ⟨k, hk⟩ := by
  simp [coordinateExtend, hk]

private theorem coordinateExtend_fin {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    coordinateExtend x i = x i :=
  coordinateExtend_lt x i.isLt

private theorem partialSum_eq_extended_sum {n : ℕ} (x : Fin n → ℝ)
    {k : ℕ} (hk : k ≤ n) :
    partialSum x k = ∑ i ∈ range k, coordinateExtend x i := by
  rw [partialSum, Finset.sum_filter]
  have heq : ∑ i : Fin n, (if (i : ℕ) < k then x i else 0) =
      ∑ i : Fin n,
        (fun j : ℕ => if j < k then coordinateExtend x j else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [coordinateExtend_fin]
  rw [heq, Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < k then coordinateExtend x j else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

/-- A vector in the closed positive root cone pairs nonnegatively with
every antitone real vector. -/
theorem closedCone_pairing_antitone {n : ℕ} {x : Fin n → ℝ}
    (hx : IsClosedPositiveRootCone x) (a : Fin n → ℝ) (ha : Antitone a) :
    0 ≤ ∑ i, x i * a i := by
  have hby := Finset.sum_range_by_parts (coordinateExtend a) (coordinateExtend x) n
  simp only [smul_eq_mul] at hby
  have hleft : ∑ i, x i * a i =
      ∑ i ∈ range n, coordinateExtend a i * coordinateExtend x i := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => coordinateExtend a i * coordinateExtend x i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coordinateExtend_fin, coordinateExtend_fin, mul_comm]
  have htotal : ∑ i ∈ range n, coordinateExtend x i = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (coordinateExtend x) n]
    simpa only [coordinateExtend_fin] using hx.1
  rw [hleft, hby, htotal, mul_zero, zero_sub, neg_nonneg]
  refine Finset.sum_nonpos fun i hi => ?_
  have hir : i < n - 1 := mem_range.mp hi
  have hi0 : i < n := by omega
  have hi1 : i + 1 < n := by omega
  rw [coordinateExtend_lt _ hi1, coordinateExtend_lt _ hi0,
    ← partialSum_eq_extended_sum x hi1.le]
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (ha (Fin.mk_le_mk.mpr (by omega))))
    (hx.2 (i + 1) (by omega) hi1)

private theorem squareDistance_identity {n : ℕ}
    (x y a b : Fin n → ℝ)
    (hrel : ∀ i, x i - a i = y i - b i) :
    ∑ i, (x i - y i) ^ 2 =
      (∑ i, y i ^ 2) - (∑ i, x i ^ 2) +
        2 * (∑ i, x i * a i) - 2 * (∑ i, x i * b i) := by
  calc
    _ = ∑ i, (y i ^ 2 - x i ^ 2 + 2 * (x i * a i) -
        2 * (x i * b i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hm := congrArg (fun z : ℝ => x i * z) (hrel i)
      nlinarith only [hm]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- One transported cone and the same-side orthogonality give a squared-norm
inequality, without choosing or modifying the permutation. -/
theorem sumSq_le_of_oneSided_cone {n : ℕ}
    (V1 V2 A1 A2 : Fin n → ℝ) (s : Equiv.Perm (Fin n))
    (horth : ∑ i, V1 i * A1 i = 0)
    (hanti : Antitone A2)
    (hcone : IsClosedPositiveRootCone (fun i => V1 (s.symm i)))
    (hrel : ∀ i, V1 (s.symm i) - A1 (s.symm i) = V2 i - A2 i) :
    (∑ i, V1 i ^ 2) ≤ ∑ i, V2 i ^ 2 := by
  have hnorm : ∑ i, V1 (s.symm i) ^ 2 = ∑ i, V1 i ^ 2 :=
    Equiv.sum_comp s.symm (fun i => V1 i ^ 2)
  have horth' : ∑ i, V1 (s.symm i) * A1 (s.symm i) = 0 := by
    rw [Equiv.sum_comp s.symm (fun i => V1 i * A1 i), horth]
  have hpair := closedCone_pairing_antitone hcone A2 hanti
  have hdist := squareDistance_identity
    (fun i => V1 (s.symm i)) V2 (fun i => A1 (s.symm i)) A2 hrel
  rw [hnorm, horth'] at hdist
  have hnonneg : 0 ≤ ∑ i, (V1 (s.symm i) - V2 i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- Two independently selected one-sided comparisons force equality of the
fine vectors under the first permutation. -/
theorem transported_eq_of_two_oneSided_cones {n : ℕ}
    (V1 V2 A1 A2 : Fin n → ℝ) (s r : Equiv.Perm (Fin n))
    (horth1 : ∑ i, V1 i * A1 i = 0)
    (horth2 : ∑ i, V2 i * A2 i = 0)
    (hanti1 : Antitone A1) (hanti2 : Antitone A2)
    (hcone1 : IsClosedPositiveRootCone (fun i => V1 (s.symm i)))
    (hcone2 : IsClosedPositiveRootCone (fun i => V2 (r.symm i)))
    (hrel1 : ∀ i, V1 (s.symm i) - A1 (s.symm i) = V2 i - A2 i)
    (hrel2 : ∀ i, V2 (r.symm i) - A2 (r.symm i) = V1 i - A1 i) :
    ∀ i, V1 (s.symm i) = V2 i := by
  have hnorm := le_antisymm
    (sumSq_le_of_oneSided_cone V1 V2 A1 A2 s horth1 hanti2 hcone1 hrel1)
    (sumSq_le_of_oneSided_cone V2 V1 A2 A1 r horth2 hanti1 hcone2 hrel2)
  have horth' : ∑ i, V1 (s.symm i) * A1 (s.symm i) = 0 := by
    rw [Equiv.sum_comp s.symm (fun i => V1 i * A1 i), horth1]
  have hpair := closedCone_pairing_antitone hcone1 A2 hanti2
  have hdist := squareDistance_identity
    (fun i => V1 (s.symm i)) V2 (fun i => A1 (s.symm i)) A2 hrel1
  rw [Equiv.sum_comp s.symm (fun i => V1 i ^ 2), hnorm, horth'] at hdist
  have hzero : ∑ i, (V1 (s.symm i) - V2 i) ^ 2 = 0 := by
    apply le_antisymm
    · linarith
    · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  intro i
  have hi : (V1 (s.symm i) - V2 i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (V1 (s.symm j) - V2 j))).mp hzero i (mem_univ i)
  nlinarith only [hi]

/-- The first permutation satisfies the inverse cone as soon as the original
first fine vector is in the cone. -/
theorem inverse_cone_of_two_oneSided_cones {n : ℕ}
    (V1 V2 A1 A2 : Fin n → ℝ) (s r : Equiv.Perm (Fin n))
    (horth1 : ∑ i, V1 i * A1 i = 0)
    (horth2 : ∑ i, V2 i * A2 i = 0)
    (hanti1 : Antitone A1) (hanti2 : Antitone A2)
    (hcone1 : IsClosedPositiveRootCone (fun i => V1 (s.symm i)))
    (hcone2 : IsClosedPositiveRootCone (fun i => V2 (r.symm i)))
    (hrel1 : ∀ i, V1 (s.symm i) - A1 (s.symm i) = V2 i - A2 i)
    (hrel2 : ∀ i, V2 (r.symm i) - A2 (r.symm i) = V1 i - A1 i)
    (hV1 : IsClosedPositiveRootCone V1) :
    IsClosedPositiveRootCone (fun i => V2 (s i)) := by
  have heq := transported_eq_of_two_oneSided_cones V1 V2 A1 A2 s r
    horth1 horth2 hanti1 hanti2 hcone1 hcone2 hrel1 hrel2
  have hfun : (fun i => V2 (s i)) = V1 := by
    funext i
    simpa only [Equiv.symm_apply_apply] using (heq (s i)).symm
  rw [hfun]
  exact hV1

end Langlands.SupportedRegularWeylComparison
