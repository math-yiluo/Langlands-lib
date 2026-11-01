import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Fintype.Option

/-! # Geometric summability for the opposing-twist cone -/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Langlands.RankinSelberg.TwoBlockLowerFixedSlice

/-- The geometric majorant on the entire integer diagonal lattice. -/
def geometricWeight {n : ℕ} (r : ℝ) (lam : Fin n → ℤ) : ℝ :=
  r ^ torusSize lam

theorem summable_geometric_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun z : ℤ => r ^ z.natAbs) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  simpa using And.intro (summable_geometric_of_lt_one hr0 hr1)
    (summable_geometric_of_lt_one hr0 hr1)

private theorem summable_fintype_prod_nonneg (I A : Type*) [Fintype I] :
    ∀ (f : I → A → ℝ), (∀ i a, 0 ≤ f i a) →
      (∀ i, Summable (f i)) →
      Summable (fun a : I → A => ∏ i, f i (a i)) := by
  classical
  apply Fintype.induction_empty_option
    (P := fun I _ => ∀ (f : I → A → ℝ), (∀ i a, 0 ≤ f i a) →
      (∀ i, Summable (f i)) →
      Summable (fun a : I → A => ∏ i, f i (a i)))
  · intro J K _ e ih f hf hs
    let : Fintype J := Fintype.ofEquiv K e.symm
    let eA : (K → A) ≃ (J → A) := Equiv.arrowCongr e.symm (Equiv.refl A)
    have h := eA.summable_iff.mpr
      (ih (fun i => f (e i)) (fun i => hf (e i)) (fun i => hs (e i)))
    convert h using 1
    ext a
    exact (e.prod_comp (fun i => f i (a i))).symm
  · intro f _ _
    exact (hasSum_fintype _).summable
  · intro J _ ih f hf hs
    have h := (hs none).mul_of_nonneg
      (ih (fun i => f (some i)) (fun i => hf (some i)) (fun i => hs (some i)))
      (hf none) (fun a => Finset.prod_nonneg (fun i _ => hf (some i) (a i)))
    have h' := (Equiv.piOptionEquivProd (β := fun _ : Option J => A)).summable_iff.mpr h
    simpa only [Function.comp_def, Equiv.piOptionEquivProd_apply, Fintype.prod_option] using h'

/-- Geometric decay in the sum of absolute exponents is summable, including
the empty diagonal lattice. -/
theorem summable_geometricWeight (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (geometricWeight (n := n) r) := by
  change Summable (fun lam : Fin n → ℤ => r ^ torusSize lam)
  have h := summable_fintype_prod_nonneg (Fin n) ℤ
    (fun _ z => r ^ z.natAbs)
    (fun _ z => pow_nonneg hr0 z.natAbs)
    (fun _ => summable_geometric_natAbs hr0 hr1)
  simpa only [torusSize, Finset.prod_pow_eq_pow_sum] using h

/-- The cone inequality converts the opposing real twist into a geometric
weight. Its multiplicative constant may depend on the cone bound and twist. -/
theorem cone_twist_le_geometricWeight {n M : ℕ} {s : Finset (Fin n)}
    {lam : Fin n → ℤ} (hcone : OppositeCone M s lam)
    {q B u : ℝ} (hq : 1 < q) (hB : 0 ≤ B) (hu : 0 ≤ u) :
    B ^ torusSize lam * q ^ (-u * (twistDegree s lam : ℝ)) ≤
      q ^ (u * (n * (2 * M) : ℕ)) * geometricWeight (B * q ^ (-u)) lam := by
  have hsize : (torusSize lam : ℝ) ≤
      (twistDegree s lam : ℝ) + (n * (2 * M) : ℕ) := by
    exact_mod_cast torusSize_le_twistDegree_add hcone
  have hexp : -u * (twistDegree s lam : ℝ) ≤
      u * (n * (2 * M) : ℕ) + (-u) * (torusSize lam : ℝ) := by
    nlinarith
  calc
    _ ≤ B ^ torusSize lam *
        q ^ (u * (n * (2 * M) : ℕ) + (-u) * (torusSize lam : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq.le hexp) (pow_nonneg hB _)
    _ = _ := by
      rw [Real.rpow_add (zero_lt_one.trans hq),
        Real.rpow_mul_natCast (zero_le_one.trans hq.le) (-u) (torusSize lam)]
      simp only [geometricWeight, mul_pow]
      ring

/-- Any nonnegative growth base has a single threshold, before all cone and
lattice data, after which the geometric ratio is less than one. -/
theorem exists_geometric_twist_threshold {q B : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, C < u → 0 ≤ u ∧ B * q ^ (-u) < 1 := by
  obtain ⟨N, hN⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop B).exists
  refine ⟨N, Nat.cast_nonneg _, fun u hu =>
    ⟨(Nat.cast_nonneg N).trans hu.le, ?_⟩⟩
  have hpow : B < q ^ u := by
    calc
      B < q ^ N := hN
      _ = q ^ (N : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ q ^ u := Real.rpow_le_rpow_of_exponent_le hq.le hu.le
  rw [Real.rpow_neg (zero_le_one.trans hq.le), ← div_eq_mul_inv]
  exact (div_lt_one (Real.rpow_pos_of_pos (zero_lt_one.trans hq) u)).mpr hpow

/-- A fixed growth base times a sufficiently strong opposing twist is
summable on every opposite cone. The threshold does not depend on that cone. -/
theorem summable_cone_twist {n M : ℕ} (s : Finset (Fin n)) {q B u : ℝ}
    (hq : 1 < q) (hB : 0 ≤ B) (hu : 0 ≤ u) (hr : B * q ^ (-u) < 1) :
    Summable (fun lam : Fin n → ℤ =>
      if OppositeCone M s lam then
        B ^ torusSize lam * q ^ (-u * (twistDegree s lam : ℝ)) else 0) := by
  classical
  have hr0 : 0 ≤ B * q ^ (-u) := mul_nonneg hB (Real.rpow_nonneg (by linarith) _)
  apply Summable.of_nonneg_of_le
    (fun lam => by split_ifs <;> positivity) _
    ((summable_geometricWeight n hr0 hr).mul_left (q ^ (u * (n * (2 * M) : ℕ))))
  intro lam
  split_ifs with hcone
  · exact cone_twist_le_geometricWeight hcone hq hB hu
  · exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg hr0 _)

end Langlands.RankinSelberg.TwoBlockLowerFixedSlice
