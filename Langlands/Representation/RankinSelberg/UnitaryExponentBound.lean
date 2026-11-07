import Langlands.Representation.RankinSelberg.UnitaryCellMasses
import Langlands.Representation.RankinSelberg.SphericalWhittakerFormula
import Langlands.Representation.RankinSelberg.SymmetricGeneratingSeries

/-!
# The exponent bound for unitary generic unramified representations
-/

noncomputable section

open Filter Topology

namespace Langlands.RankinSelberg.UnramifiedUnitary

/-! ### Decay of a series inverse to a polynomial -/

section Decay

/-- If `∑ u_m t^m` is inverse to `∏ (1 - b_i t)` and `u_m → 0`, then every `|b_i| < 1`. -/
theorem norm_lt_one_of_mul_prod_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ℕ → ℂ)
    (b : ι → ℂ)
    (hinv : PowerSeries.mk u * ∏ i, (1 - PowerSeries.C (b i) * PowerSeries.X) = 1)
    (hu : Tendsto u atTop (𝓝 0)) (i : ι) : ‖b i‖ < 1 := by
  -- the cofactor, a polynomial
  let g : Polynomial ℂ := ∏ j ∈ Finset.univ.erase i, (1 - Polynomial.C (b j) * Polynomial.X)
  have hg : ((g : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ j ∈ Finset.univ.erase i, (1 - PowerSeries.C (b j) * PowerSeries.X) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    apply Finset.prod_congr rfl
    intro j _
    rw [Polynomial.coeToPowerSeries.ringHom_apply]
    simp
  -- the geometric series of `b i`
  have hgeom : PowerSeries.mk (fun m => b i ^ m) * (1 - PowerSeries.C (b i) * PowerSeries.X) = 1 := by
    have h := congrArg (PowerSeries.rescale (b i)) (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
    simpa [PowerSeries.rescale_mk, PowerSeries.rescale_X, smul_eq_mul] using h
  have hsplit : PowerSeries.mk u * (g : PowerSeries ℂ) * (1 - PowerSeries.C (b i) * PowerSeries.X)
      = 1 := by
    rw [hg, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    exact hinv
  have heq : PowerSeries.mk u * (g : PowerSeries ℂ) = PowerSeries.mk (fun m => b i ^ m) := by
    calc PowerSeries.mk u * (g : PowerSeries ℂ)
        = PowerSeries.mk u * (g : PowerSeries ℂ) *
            ((1 - PowerSeries.C (b i) * PowerSeries.X) * PowerSeries.mk (fun m => b i ^ m)) := by
          rw [mul_comm (1 - _) _, hgeom, mul_one]
      _ = PowerSeries.mk (fun m => b i ^ m) := by
          rw [← mul_assoc, hsplit, one_mul]
  -- coefficients of the product
  have heq' : (g : PowerSeries ℂ) * PowerSeries.mk u = PowerSeries.mk (fun m => b i ^ m) := by
    rw [mul_comm]
    exact heq
  set N := g.natDegree
  have hcoeff : ∀ m, N ≤ m → b i ^ m = ∑ c ∈ Finset.range (N + 1), g.coeff c * u (m - c) := by
    intro m hm
    have h := congrArg (PowerSeries.coeff m) heq'
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a c =>
        PowerSeries.coeff a (g : PowerSeries ℂ) * PowerSeries.coeff c (PowerSeries.mk u))] at h
    rw [← h]
    have hsub : Finset.range (N + 1) ⊆ Finset.range (m + 1) :=
      Finset.range_subset_range.mpr (Nat.succ_le_succ hm)
    symm
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro c _
      rw [Polynomial.coeff_coe, PowerSeries.coeff_mk]
    · intro c _ hcN
      have hlt : N < c := by
        rw [Finset.mem_range, not_lt] at hcN
        omega
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
  -- the right side tends to zero
  have hlim : Tendsto (fun m => ∑ c ∈ Finset.range (N + 1), g.coeff c * u (m - c)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (N + 1)) (fun c _ =>
      (hu.comp (tendsto_sub_atTop_nat c)).const_mul (g.coeff c))
    simpa using this
  have hpow : Tendsto (fun m => b i ^ m) atTop (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    exact (hcoeff m hm).symm
  by_contra hge
  push Not at hge
  have hnorm : Tendsto (fun m => ‖b i ^ m‖) atTop (𝓝 0) := by
    simpa using hpow.norm
  have hone : ∀ m, (1 : ℝ) ≤ ‖b i ^ m‖ := fun m => by
    rw [norm_pow]
    exact one_le_pow₀ hge
  have := ge_of_tendsto hnorm (Eventually.of_forall hone)
  linarith

end Decay

/-! ### Single-row Schur functions -/

section SingleRow

open MvPolynomial GeneralLinear.Spherical

/-- The exponent `(m, 0, …, 0)` of `GL_(n+2)`. -/
def rowExponent (n m : ℕ) : Fin (n + 2) → ℤ := fun i => if i = 0 then (m : ℤ) else 0

theorem rowExponent_isPartition (n m : ℕ) : UnramifiedWhittaker.IsPartitionExponent (rowExponent n m) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · by_cases hj : j = 0
    · have hi : i = 0 := le_antisymm (hj ▸ hij) (Fin.zero_le _)
      rw [hi, hj]
    · simp only [rowExponent, ite_eq_right hj]
      split_ifs <;> omega
  · simp only [rowExponent]
    split_ifs <;> omega

theorem rowExponent_last (n m : ℕ) : rowExponent n m (Fin.last (n + 1)) = 0 :=
  ite_eq_right (Fin.last_pos.ne')

/-- The Jacobi–Trudi determinant of a single row is the complete symmetric polynomial. -/
theorem jacobiTrudi_rowExponent (n m : ℕ) :
    jacobiTrudi ℂ (rowExponent n m) = hsymm (Fin (n + 2)) ℂ m := by
  rw [jacobiTrudi, Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_succ]
    have h1 : ∏ i : Fin (n + 1), (Matrix.of fun i j : Fin (n + 2) =>
        completeSymm (Fin (n + 2)) ℂ (rowExponent n m i - i + j)) i.succ i.succ = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [rowExponent, completeSymm, hsymm_zero, Fin.succ_ne_zero]
    rw [h1, mul_one]
    simp [rowExponent, completeSymm]
  · intro i j hji
    have hlt : (j : ℕ) < (i : ℕ) := hji
    have hi : i ≠ 0 := by
      intro h
      rw [h] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
    have : ¬ (0 : ℤ) ≤ rowExponent n m i - (i : ℤ) + j := by
      simp only [rowExponent, ite_eq_right hi]
      omega
    rw [Matrix.of_apply, completeSymm, ite_eq_right this]

theorem satakeSchur_rowExponent {n : ℕ} (x : Fin (n + 2) → ℂˣ) (m : ℕ) :
    satakeSchur x (rowExponent n m) = eval (fun i => (x i : ℂ)) (hsymm (Fin (n + 2)) ℂ m) := by
  rw [satakeSchur, rowExponent_last, zpow_zero, one_mul]
  simp only [sub_zero]
  rw [jacobiTrudi_rowExponent]

theorem halfModulus_rowExponent (q n m : ℕ) :
    halfModulus q (rowExponent n m) = ((Real.sqrt q : ℝ) : ℂ) ^ (-(((n + 1 : ℕ) : ℤ) * m)) := by
  rw [halfModulus]
  congr 2
  rw [Fin.sum_univ_succ]
  have h0 : ∑ i : Fin (n + 1), (((n + 1 : ℕ) : ℤ) - 2 * ((i.succ : Fin (n + 2)) : ℤ)) *
      rowExponent n m i.succ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [rowExponent, Fin.succ_ne_zero]
  rw [h0, add_zero]
  simp [rowExponent]

theorem rescale_C_eq (c a : ℂ) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst h
    simp
  · rw [mul_zero]

/-- The rescaled evaluated complete series is inverse to `∏ (1 - a_i c t)`. -/
theorem hsymm_series_mul_prod {σ : Type*} [Fintype σ] [DecidableEq σ] (a : σ → ℂ) (c : ℂ) :
    PowerSeries.mk (fun m => c ^ m * eval a (hsymm σ ℂ m)) *
      ∏ i, (1 - PowerSeries.C (a i * c) * PowerSeries.X) = 1 := by
  have h := congrArg (fun f => PowerSeries.rescale c (PowerSeries.map (eval a) f))
    (completeSeries_mul_elementaryProduct σ ℂ)
  simp only [map_mul, map_prod, map_sub, map_one] at h
  have h1 : PowerSeries.map (eval a) (completeSeries σ ℂ) =
      PowerSeries.mk (fun m => eval a (hsymm σ ℂ m)) := by
    ext m
    rw [PowerSeries.coeff_map, completeSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rw [h1, PowerSeries.rescale_mk] at h
  convert h using 2
  apply Finset.prod_congr rfl
  intro i _
  rw [PowerSeries.map_C, PowerSeries.map_X, rescale_C_eq, PowerSeries.rescale_X, eval_X,
    ← mul_assoc, ← map_mul]

end SingleRow

/-! ### The exponent bound for characters of conductor `O` -/

section Bound

open GeneralLinear GeneralLinear.Spherical Whittaker Conductor Correspondence HarmonicAnalysis
  Unramified MvPolynomial

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance boundFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance boundFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance boundFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- **The unitary exponent bound** (for `ψ` of conductor `O`). For a unitarizable
unramified generic constituent `π` of `GL_(k+2)(F)` with inducing characters `χ`, every
Satake parameter satisfies `|χ_i(ϖ)| < q^(1/2)`. -/
theorem norm_characterValues_lt_sqrt (k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductor ψ)
    (χ : Fin (k + 1 + 1) → QuasiCharacter F)
    (hgen : IsUnramifiedGenericConstituent F ψ π χ) (hunit : IsUnitarizable π)
    (i : Fin (k + 1 + 1)) :
    ‖((Unramified.characterValues F χ i : ℂˣ) : ℂ)‖ <
      Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) := by
  classical
  have hirr : Representation.IsIrreducible π := hgen.1.1
  have hadm : IsAdmissible π := hgen.1.2.1
  obtain ⟨ℓ, hℓ⟩ := hgen.1.2.2
  obtain ⟨w, -⟩ := (Langlands.RankinSelberg.unramifiedSphericalVector p F (k + 1) π ψ hψ hgen.1
    hgen.2.1).1 ℓ hℓ
  obtain ⟨v, hv⟩ := modelMap_surjective π ℓ w.val.val
  have hval (g : Langlands.GeneralLinear (k + 1 + 1) F.Carrier) :
      sphericalTestFunction π ℓ w g = ℓ.val (π g v) :=
    (congrArg (fun u : (coefficientModel π ℓ).toSubmodule => u.val.val g) hv).symm
  have hvK : v ∈ fixedVectors π (sphericalSubgroup F (k + 1)) :=
    UnramifiedWhittaker.mem_fixedVectors_of_model F π ℓ (modelEquiv π ℓ hℓ).injective v
      (by rw [hv]; exact (mem_sphericalModelSpace π ℓ w.val.val).mp w.val.property)
  obtain ⟨C, hC⟩ := rowSum_bounded F k ψ π hadm hirr hunit ℓ hℓ v hvK
  set q := F.canonicalTopologicalData.residueCardinality
  set sq := Real.sqrt (q : ℝ) with hsq
  have hq : (0 : ℝ) < q := by
    exact_mod_cast (lt_trans Nat.zero_lt_one F.canonicalTopologicalData.residueCardinality_gt_one)
  have hs : 0 < sq := Real.sqrt_pos.mpr hq
  have hs2 : sq ^ 2 = q := Real.sq_sqrt hq.le
  let a : Fin (k + 1 + 1) → ℂ := fun j => (Unramified.characterValues F χ j : ℂ)
  let c : ℂ := ((sq : ℝ) : ℂ)⁻¹
  let u : ℕ → ℂ := fun m => c ^ m * eval a (hsymm (Fin (k + 1 + 1)) ℂ m)
  have hform (m : ℕ) :
      ℓ.val (π (Iwasawa.torus F.canonicalTopologicalData.uniformizerUnit
        (fun i : Fin (k + 1 + 1) => if i = 0 then (m : ℤ) else 0)) v) =
        halfModulus q (rowExponent k m) * eval a (hsymm (Fin (k + 1 + 1)) ℂ m) := by
    rw [← hval]
    rw [show (fun i : Fin (k + 1 + 1) => if i = 0 then (m : ℤ) else 0) = rowExponent k m from rfl,
      UnramifiedWhittaker.sphericalTest_torus_schur F π ψ hψ χ hgen ℓ hℓ w _
        (rowExponent_isPartition k m), satakeSchur_rowExponent]
  have hu2 (m : ℕ) : (q : ℝ) ^ (k * m) *
      ‖ℓ.val (π (Iwasawa.torus F.canonicalTopologicalData.uniformizerUnit
        (fun i : Fin (k + 1 + 1) => if i = 0 then (m : ℤ) else 0)) v)‖ ^ 2 = ‖u m‖ ^ 2 := by
    rw [hform, halfModulus_rowExponent, norm_mul, norm_mul, norm_pow, norm_zpow, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg hs.le]
    set H := ‖eval a (hsymm (Fin (k + 1 + 1)) ℂ m)‖
    rw [← hs2, zpow_neg, zpow_mul, zpow_natCast, zpow_natCast]
    field_simp
    have hBC : sq ^ (m * 2) * sq⁻¹ ^ (m * 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow]
    linear_combination (-(sq ^ (k * m * 2) * H ^ 2)) * hBC
  have hsum (M : ℕ) : ∑ m ∈ Finset.range M, ‖u m‖ ^ 2 ≤ C := by
    rw [← Finset.sum_congr rfl (fun m _ => hu2 m)]
    exact hC M
  have hsumm : Summable (fun m => ‖u m‖ ^ 2) :=
    summable_of_sum_range_le (fun m => sq_nonneg _) hsum
  have hlim : Tendsto u atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (Real.continuous_sqrt.tendsto 0).comp hsumm.tendsto_atTop_zero
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h
  have hb := norm_lt_one_of_mul_prod_eq_one u (fun j => a j * c) (hsymm_series_mul_prod a c)
    hlim i
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le] at hb
  have h := (mul_inv_lt_iff₀ hs).1 hb
  rw [one_mul] at h
  exact h

end Bound

end Langlands.RankinSelberg.UnramifiedUnitary
