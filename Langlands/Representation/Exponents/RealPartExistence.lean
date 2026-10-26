import Langlands.Group.GL.UnramifiedCharacter
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Existence of real parts of split-centre characters

A character of `(F^×)^r` with open kernel has a real part: there is `x : Fin r → ℝ`
with `|χ(a)| = ∏ |a_i|^(x_i)`. On each coordinate the character is trivial on an
open subgroup of the compact group of norm-one units, so its absolute value is one
there, and its absolute value is determined by the value at the uniformizer.
-/

noncomputable section

namespace Langlands

universe uF

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A character of `F^×` with open kernel has absolute value one on the norm-one units. -/
theorem norm_eq_one_of_isOpen_ker (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ)) {u : F.Carrierˣ}
    (hu : u ∈ T.normalizedAbsUnits.ker) : ‖(χ u : ℂ)‖ = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let K := T.normalizedAbsUnits.ker
  have : CompactSpace K :=
    isCompact_iff_compactSpace.mp (CuspidalSupport.isCompact_ker_normalizedAbsUnits T)
  let U : Subgroup K := χ.ker.subgroupOf K
  have hU : IsOpen (U : Set K) := Subgroup.subgroupOf_isOpen K χ.ker hχ
  have : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  have hmem := U.pow_index_mem ⟨u, hu⟩
  have h1 : χ u ^ U.index = 1 := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    rw [Subgroup.coe_pow, MonoidHom.mem_ker, map_pow] at h
    exact h
  have h2 : ‖(χ u : ℂ)‖ ^ U.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) U.index_ne_zero_of_finite).mp h2

/-- A character of `F^×` with open kernel has absolute value `|χ(ϖ)|^ord(a)`. -/
theorem norm_eq_zpow_ord_of_isOpen_ker (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ)) (a : F.Carrierˣ) :
    ‖(χ a : ℂ)‖ = ‖(χ T.uniformizerUnit : ℂ)‖ ^ T.ord (a : F.Carrier) := by
  set k := T.ord (a : F.Carrier)
  let u : F.Carrierˣ := a * T.uniformizerUnit ^ (-k)
  have hu : u ∈ T.normalizedAbsUnits.ker := by
    rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj]
    change T.normalizedAbs ((a * T.uniformizerUnit ^ (-k) : F.Carrierˣ) : F.Carrier) = 1
    have hq : (T.residueCardinality : ℝ) ≠ 0 := by
      exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
    rw [Units.val_mul, T.normalizedAbs_mul, T.normalizedAbs_of_ne_zero a.ne_zero,
      LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs, neg_neg, ← zpow_add₀ hq,
      neg_add_cancel, zpow_zero]
  have ha : a = u * T.uniformizerUnit ^ k := by
    simp only [u, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [ha, map_mul, map_zpow, Units.val_mul, norm_mul, T.norm_eq_one_of_isOpen_ker χ hχ hu,
    one_mul, Units.val_zpow_eq_zpow_val, norm_zpow]

/-- A character of `F^×` with open kernel has real part `-log_q |χ(ϖ)|`. -/
theorem norm_eq_normalizedAbs_rpow_of_isOpen_ker (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ)) (a : F.Carrierˣ) :
    ‖(χ a : ℂ)‖ = T.normalizedAbs (a : F.Carrier) ^
      (-Real.logb T.residueCardinality ‖(χ T.uniformizerUnit : ℂ)‖) := by
  have hq1 : (1 : ℝ) < T.residueCardinality := T.one_lt_residueCardinality_real
  have hq0 : (0 : ℝ) < T.residueCardinality := lt_trans zero_lt_one hq1
  have hc : 0 < ‖(χ T.uniformizerUnit : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  rw [T.norm_eq_zpow_ord_of_isOpen_ker χ hχ a, T.normalizedAbs_of_ne_zero a.ne_zero,
    ← Real.rpow_intCast (T.residueCardinality : ℝ), ← Real.rpow_mul hq0.le]
  set c := ‖(χ T.uniformizerUnit : ℂ)‖
  set k := T.ord (a : F.Carrier)
  have hk : ((-k : ℤ) : ℝ) * -Real.logb T.residueCardinality c =
      Real.logb T.residueCardinality c * (k : ℝ) := by
    push_cast
    ring
  rw [hk, Real.rpow_mul hq0.le, Real.rpow_logb hq0 hq1.ne' hc, Real.rpow_intCast]

/-- Every character of `(F^×)^r` with open kernel has a real part. -/
theorem exists_isRealPartOf {r : ℕ} (χ : (Fin r → F.Carrierˣ) →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set (Fin r → F.Carrierˣ))) :
    ∃ x : Fin r → ℝ, T.IsRealPartOf χ x := by
  let := T.topology
  classical
  let χi : Fin r → (F.Carrierˣ →* ℂˣ) := fun i => χ.comp (MonoidHom.mulSingle (fun _ : Fin r => F.Carrierˣ) i)
  have hχi : ∀ i, IsOpen ((χi i).ker : Set F.Carrierˣ) := fun i =>
    hχ.preimage (continuous_mulSingle i)
  refine ⟨fun i => -Real.logb T.residueCardinality ‖(χi i T.uniformizerUnit : ℂ)‖, ?_⟩
  intro a
  have hprod : χ a = ∏ i, χi i (a i) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle a]
    rw [map_prod]
    rfl
  rw [hprod, Units.coe_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ =>
    T.norm_eq_normalizedAbs_rpow_of_isOpen_ker (χi i) (hχi i) (a i)

end PadicField.TopologicalData

end Langlands
