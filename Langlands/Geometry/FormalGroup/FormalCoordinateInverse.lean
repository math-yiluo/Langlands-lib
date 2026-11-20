import Langlands.Geometry.FormalGroup.Tangent
import Mathlib.RingTheory.MvPowerSeries.PiTopology

/-! # Formal inversion for a coordinate map tangent to the identity -/

noncomputable section

universe u

namespace Langlands.FormalGroup.CoordinateMap

open MvPowerSeries MvPowerSeries.WithPiTopology Finset
open scoped MvPowerSeries.WithPiTopology

variable {R : Type u} [CommRing R] {σ : Type} [Finite σ]

omit [Finite σ] in
private theorem order_mul_lower_bound {a b : MvPowerSeries σ R} {n m : ℕ}
    (ha : (n : ℕ∞) ≤ a.order) (hb : (m : ℕ∞) ≤ b.order) :
    ((n + m : ℕ) : ℕ∞) ≤ (a * b).order := by
  rw [Nat.cast_add]
  exact (add_le_add ha hb).trans (le_order_mul)

omit [Finite σ] in
private theorem order_mul_sub_mul {a a' b b' : MvPowerSeries σ R} {n m : ℕ}
    (ha' : (n : ℕ∞) ≤ a'.order) (hb : (m : ℕ∞) ≤ b.order)
    (ha : ((n + 1 : ℕ) : ℕ∞) ≤ (a - a').order)
    (hb' : ((m + 1 : ℕ) : ℕ∞) ≤ (b - b').order) :
    ((n + m + 1 : ℕ) : ℕ∞) ≤ (a * b - a' * b').order := by
  rw [show a * b - a' * b' = (a - a') * b + a' * (b - b') by ring]
  apply le_trans _ min_order_le_add
  apply le_min
  · simpa only [Nat.add_right_comm] using order_mul_lower_bound ha hb
  · simpa only [Nat.add_assoc] using order_mul_lower_bound ha' hb'

omit [Finite σ] in
private theorem order_pow_sub_pow {a b : MvPowerSeries σ R}
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (hd : 2 ≤ (a - b).order) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (a ^ n - b ^ n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact order_mul_sub_mul (le_order_pow_of_constantCoeff_eq_zero n hb)
      (one_le_order_iff_constCoeff_eq_zero.mpr ha) ih hd

omit [Finite σ] in
private theorem order_prod_sub_prod {ι : Type} (s : Finset ι) (k : ι → ℕ)
    (a b : ι → MvPowerSeries σ R)
    (ha : ∀ i, (k i : ℕ∞) ≤ (a i).order)
    (hb : ∀ i, (k i : ℕ∞) ≤ (b i).order)
    (hd : ∀ i, ((k i + 1 : ℕ) : ℕ∞) ≤ (a i - b i).order) :
    ((∑ i ∈ s, k i) + 1 : ℕ) ≤ ((∏ i ∈ s, a i) - ∏ i ∈ s, b i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    have hs : ((∑ j ∈ s, k j : ℕ) : ℕ∞) ≤ (∏ j ∈ s, a j).order := by
      rw [Nat.cast_sum]
      exact (Finset.sum_le_sum fun j _ => ha j).trans (le_order_prod a s)
    exact order_mul_sub_mul (hb i) hs (hd i) ih

private def substitutionCorrection (f : CoordinateMap R σ σ) :
    MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R :=
  LinearMap.id - (substAlgHom f.hasSubst).toLinearMap

private theorem substitutionCorrection_apply (f : CoordinateMap R σ σ) (p : MvPowerSeries σ R) :
    substitutionCorrection f p = p - subst f.series p := by
  simp only [substitutionCorrection, LinearMap.sub_apply, LinearMap.id_apply,
    AlgHom.toLinearMap_apply, substAlgHom_apply]

/-- If the coordinate series agree with the variables in degrees zero and one,
subtracting substitution from the identity raises order by at least one. -/
private theorem order_substitutionCorrection (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order)
    (p : MvPowerSeries σ R) (n : ℕ) (hp : (n : ℕ∞) ≤ p.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (substitutionCorrection f p).order := by
  classical
  apply nat_le_order
  intro d hd
  rw [substitutionCorrection_apply]
  have hX : subst (R := R) (σ := σ) X p = p :=
    congrFun (subst_self (R := R)) p
  have hXSubst : HasSubst (fun i : σ => (X i : MvPowerSeries σ R)) := HasSubst.X
  have hcX := coeff_subst_finite hXSubst p d
  have hcf := coeff_subst_finite f.hasSubst p d
  rw [map_sub]
  nth_rw 1 [← hX]
  rw [coeff_subst hXSubst, coeff_subst f.hasSubst, ← finsum_sub_distrib hcX hcf]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases he : e.degree < n
  · have hpe : coeff e p = 0 := coeff_of_lt_order ((ENat.natCast_lt_natCast.mpr he).trans_le hp)
    simp only [hpe, zero_smul, sub_zero]
  · rw [← smul_sub, ← map_sub]
    have hprod : ((e.degree + 1 : ℕ) : ℕ∞) ≤
        ((e.prod fun i k => X i ^ k) - e.prod (fun i k => f.series i ^ k)).order := by
      rw [Finsupp.prod, Finsupp.prod, Finsupp.degree_apply]
      exact order_prod_sub_prod e.support e
        (fun i => X i ^ e i) (fun i => f.series i ^ e i)
        (fun i => le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_X i))
        (fun i => le_order_pow_of_constantCoeff_eq_zero _ (f.constantCoeff_eq_zero i))
        (fun i => order_pow_sub_pow (constantCoeff_X i) (f.constantCoeff_eq_zero i) (hf i) _)
    rw [coeff_of_lt_order (lt_of_lt_of_le ?_ hprod), smul_zero]
    exact ENat.natCast_lt_natCast.mpr (lt_of_lt_of_le hd (Nat.succ_le_succ (Nat.le_of_not_gt he)))

private theorem substAlgHom_injective (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order) :
    Function.Injective (substAlgHom f.hasSubst : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R) := by
  intro p q hpq
  let z := p - q
  have hz : substAlgHom f.hasSubst z = 0 := by
    rw [show z = p - q from rfl, map_sub, hpq, sub_self]
  have hfixed : substitutionCorrection f z = z := by
    change z - substAlgHom f.hasSubst z = z
    rw [hz, sub_zero]
  have horder (n : ℕ) : (n : ℕ∞) ≤ z.order := by
    induction n with
    | zero => exact zero_le
    | succ n ih =>
      simpa only [hfixed] using order_substitutionCorrection f hf z n ih
  apply sub_eq_zero.mp
  change z = 0
  apply MvPowerSeries.ext
  intro d
  rw [coeff_zero]
  exact coeff_of_lt_order ((ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self d.degree)).trans_le
    (horder (d.degree + 1)))

private theorem substAlgHom_surjective (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order) :
    Function.Surjective (substAlgHom f.hasSubst : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R) := by
  let : UniformSpace R := ⊥
  intro q
  let step : ℕ → MvPowerSeries σ R := fun n => (substitutionCorrection f)^[n] q
  have horder (n : ℕ) : (n : ℕ∞) ≤ (step n).order := by
    induction n with
    | zero => exact zero_le
    | succ n ih =>
      rw [show step (n + 1) = substitutionCorrection f (step n) from
        Function.iterate_succ_apply' _ _ _]
      exact order_substitutionCorrection f hf _ n ih
  have hs : Summable step := by
    apply summable_of_tendsto_order_atTop_nhds_top
    rw [ENat.tendsto_nhds_top_iff_natCast_lt]
    intro n
    exact Filter.eventually_atTop.mpr ⟨n + 1, fun k hk =>
      (ENat.natCast_lt_natCast.mpr (Nat.lt_of_succ_le hk)).trans_le (horder k)⟩
  refine ⟨∑' n, step n, ?_⟩
  have hcont : Continuous (substitutionCorrection f) := by
    change Continuous (fun p => substitutionCorrection f p)
    simp only [substitutionCorrection_apply]
    exact continuous_id.sub (continuous_subst (R := R) f.hasSubst)
  have htail : (∑' n, step (n + 1)) = substitutionCorrection f (∑' n, step n) := by
    have h := (hs.hasSum.map (substitutionCorrection f).toAddMonoidHom hcont).tsum_eq
    simpa only [step, Function.iterate_succ_apply', LinearMap.toAddMonoidHom_coe,
      Function.comp_apply] using h
  have hsum := hs.tsum_eq_zero_add
  change (∑' n, step n) = q + (∑' n, step (n + 1)) at hsum
  rw [htail, substitutionCorrection_apply] at hsum
  rw [substAlgHom_apply]
  linear_combination hsum

private def substitutionEquiv (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order) :
    MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R :=
  AlgEquiv.ofBijective (substAlgHom f.hasSubst)
    ⟨substAlgHom_injective f hf, substAlgHom_surjective f hf⟩

private theorem subst_equiv_symm (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order) (p : MvPowerSeries σ R) :
    subst f.series ((substitutionEquiv f hf).symm p) = p :=
  (substAlgHom_apply f.hasSubst _).symm.trans ((substitutionEquiv f hf).apply_symm_apply p)

/-- Inverse pointed coordinates for a map whose series agree with the variables
in degrees zero and one. -/
def inverseOfIdentityLinear (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order) : CoordinateMap R σ σ where
  series i := (substitutionEquiv f hf).symm (X i)
  constantCoeff_eq_zero i := by
    have h := order_substitutionCorrection f hf ((substitutionEquiv f hf).symm (X i))
      0 zero_le
    rw [substitutionCorrection_apply, subst_equiv_symm f hf] at h
    simpa only [Nat.zero_add, Nat.cast_one, one_le_order_iff_constCoeff_eq_zero,
      map_sub, constantCoeff_X, sub_zero] using h

@[simp]
theorem inverseOfIdentityLinear_comp (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order) :
    (f.inverseOfIdentityLinear hf).comp f = CoordinateMap.id := by
  apply CoordinateMap.ext
  funext i
  exact subst_equiv_symm f hf (X i)

@[simp]
theorem comp_inverseOfIdentityLinear (f : CoordinateMap R σ σ)
    (hf : ∀ i, 2 ≤ (X i - f.series i).order) :
    f.comp (f.inverseOfIdentityLinear hf) = CoordinateMap.id := by
  have h : (f.comp (f.inverseOfIdentityLinear hf)).comp f = CoordinateMap.id.comp f := by
    rw [comp_assoc, inverseOfIdentityLinear_comp, comp_id, id_comp]
  apply CoordinateMap.ext
  funext i
  apply substAlgHom_injective f hf
  rw [substAlgHom_apply, substAlgHom_apply]
  exact congrArg (fun g : CoordinateMap R σ σ => g.series i) h

/-- Identity tangent and zero constant terms give agreement in degrees zero and one. -/
theorem order_variable_sub_of_linearPart_id (f : CoordinateMap R σ σ)
    (hf : f.linearPart = LinearMap.id) (i : σ) : 2 ≤ (X i - f.series i).order := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  change ((2 : ℕ) : ℕ∞) ≤ (X i - f.series i).order
  apply nat_le_order
  intro d hd
  by_cases hzero : d.degree = 0
  · rw [(Finsupp.degree_eq_zero_iff d).mp hzero, map_sub, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_X, f.constantCoeff_eq_zero, sub_zero]
  · have hdeg : d.degree = 1 := by omega
    have hm : d ∈ Set.range (fun j : σ => Finsupp.single j 1) := by
      rwa [Finsupp.range_single_one]
    obtain ⟨j, rfl⟩ := hm
    have h := congrFun (LinearMap.congr_fun (hf.trans linearPart_id.symm) (Pi.single j 1)) i
    simp only [linearPart_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    rw [map_sub]
    exact sub_eq_zero.mpr h.symm

end Langlands.FormalGroup.CoordinateMap
