import Langlands.Representation.RankinSelberg.UnipotentDiagonalVolume
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.AllField.Representation.Whittaker.JPSDilationAssemblyProof
/-!
# Unipotent volume of a compact set of matrices along a diagonal translate

For a `p`-adic field with its canonical topology and a compact set `L` of
square matrices, the Haar volume of `{u ∈ N | u · diag(a) ∈ L}` is bounded by a
constant times a monomial in `|a_i|⁻¹`, and the set is empty unless every
`|a_i|` is bounded. See the paired Markdown for the route.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding diagonalConj_map singleton_modulus_real unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear

universe uF

namespace UnipotentDiagonalVolume
open Langlands.RankinSelberg.UnipotentDiagonalVolume hiding normalizedAbs_units_pow normalizedAbs_units_prod
open Langlands.AllField.RankinSelberg.UnipotentDiagonalVolume
open Langlands.RankinSelberg hiding diagonalConj_map singleton_modulus_real unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel
open Langlands.AllField.RankinSelberg

variable {F : Type uF} [Field F]

/-- The normalized absolute value of a power of a unit. -/
theorem normalizedAbs_units_pow (T : LocalFieldData F) (x : Fˣ) (k : ℕ) :
    T.normalizedAbs ((x ^ k : Fˣ) : F) =
      T.normalizedAbs (x : F) ^ k := by
  rw [Units.val_pow_eq_pow_val]
  induction k with
  | zero => simp [T.normalizedAbs_one]
  | succ k ih => rw [pow_succ, T.normalizedAbs_mul, ih, pow_succ]

/-- The normalized absolute value of a product of units. -/
theorem normalizedAbs_units_prod (T : LocalFieldData F) {ι : Type*} (s : Finset ι)
    (x : ι → Fˣ) :
    T.normalizedAbs ((∏ k ∈ s, x k : Fˣ) : F) =
      ∏ k ∈ s, T.normalizedAbs (x k : F) := by
  rw [← T.normalizedAbsUnits_coe, map_prod, Units.coe_prod, NNReal.coe_prod]
  rfl

end UnipotentDiagonalVolume

open Langlands.RankinSelberg.UnipotentDiagonalVolume hiding normalizedAbs_units_pow normalizedAbs_units_prod
open Langlands.AllField.RankinSelberg.UnipotentDiagonalVolume

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {F}

/-- **Unipotent volume along a diagonal translate.** For a compact set `L` of
matrices there are a unit `r`, a constant `C` and exponents `e` such that, for
every diagonal `a`, if some `u · diag(a)` with `u` upper unipotent lies in `L`
then every `|a_i| ≤ |r|`, and the unipotent Haar volume of the `u` with
`u · diag(a) ∈ L` is at most `C ∏ |a_i|⁻¹ ^ e_i`. -/
theorem unipotentHaar_mul_diagonal_le (n : ℕ)
    [MeasurableSpace (upperUnipotent (n + 1) F)]
    [BorelSpace (upperUnipotent (n + 1) F)]
    (L : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) (hL : IsCompact L) :
    ∃ (r : Fˣ) (C : ℝ) (e : Fin (n + 1) → ℕ), ∀ a : Fin (n + 1) → Fˣ,
      ((∃ u : upperUnipotent (n + 1) F,
          u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L) →
        ∀ i, (⟨⟩ : LocalFieldData F).normalizedAbs (a i : F) ≤
          (⟨⟩ : LocalFieldData F).normalizedAbs (r : F)) ∧
      unipotentHaar F n
          {u | u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L} ≤
        ENNReal.ofReal (C * ∏ i,
          ((⟨⟩ : LocalFieldData F).normalizedAbs (a i : F))⁻¹ ^ e i) := by
  set T := (⟨⟩ : LocalFieldData F) with hT
  -- A bound for the entries of the matrices in `L`.
  have hcont : Continuous fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F =>
      ∑ i, ∑ j, T.normalizedAbs (M i j) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      T.continuous_normalizedAbs.comp (continuous_id.matrix_elem i j)
  obtain ⟨R, hR⟩ := hL.bddAbove_image hcont.continuousOn
  have hentry : ∀ M ∈ L, ∀ i j, T.normalizedAbs (M i j) ≤ R := by
    intro M hM i j
    refine le_trans ?_ (hR ⟨M, hM, rfl⟩)
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
      T.normalizedAbs_nonneg (M i j)) (Finset.mem_univ i))
    exact Finset.single_le_sum (fun j _ => T.normalizedAbs_nonneg (M i j)) (Finset.mem_univ j)
  -- The unit `r`.
  have hq : (1 : ℝ) < T.residueCardinality := Nat.one_lt_cast.mpr T.residueCardinality_gt_one
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R hq
  let r : Fˣ := Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ (-(m : ℤ))
  set ρ := T.normalizedAbs (r : F) with hρdef
  have hρ : ρ = (T.residueCardinality : ℝ) ^ m := by
    rw [hρdef, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs, neg_neg, zpow_natCast]
  have hρpos : 0 < ρ := T.normalizedAbs_pos r.ne_zero
  have hRρ : R ≤ ρ := hρ ▸ hm.le
  -- The exponent.
  let D : ℕ := ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
    (j.val - i.val)
  refine ⟨r, ρ ^ ((n + 1) * D), fun _ => D, fun a => ?_⟩
  -- Entries of `u · diag(a)`.
  have hmul : ∀ (u : upperUnipotent (n + 1) F) (i j : Fin (n + 1)),
      (u.val.val * Matrix.diagonal (fun i => (a i : F))) i j =
        u.val.val i j * (a j : F) := fun u i j => Matrix.mul_diagonal _ _ _ _
  have hbound : (∃ u : upperUnipotent (n + 1) F,
      u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L) →
      ∀ i, T.normalizedAbs (a i : F) ≤ ρ := by
    rintro ⟨u, hu⟩ i
    have h := hentry _ hu i i
    rw [hmul, show u.val.val i i = 1 from UpperUnipotent.entry_diag u i, one_mul] at h
    exact h.trans hRρ
  refine ⟨hbound, ?_⟩
  by_cases hS : ∃ u : upperUnipotent (n + 1) F,
      u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L
  swap
  · have hempty : {u : upperUnipotent (n + 1) F |
        u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun u hu => hS ⟨u, hu⟩
    rw [hempty, measure_empty]
    exact zero_le
  have ha := hbound hS
  -- The contraction parameter `t = ∏ a_k / r`, with `|t| ≤ |a_j / r| ≤ 1`.
  let t : Fˣ := ∏ k, a k * r⁻¹
  set x := T.normalizedAbs (t : F) with hxdef
  have hx : x = ∏ k, T.normalizedAbs (a k : F) * ρ⁻¹ := by
    rw [hxdef, normalizedAbs_units_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_mul, T.normalizedAbs_mul, Langlands.AllField.Whittaker.JPSDilationAssembly.normalizedAbs_units_inv]
  have hfac_nonneg : ∀ k, 0 ≤ T.normalizedAbs (a k : F) * ρ⁻¹ := fun k =>
    mul_nonneg (T.normalizedAbs_nonneg _) (inv_nonneg.mpr hρpos.le)
  have hfac_le : ∀ k, T.normalizedAbs (a k : F) * ρ⁻¹ ≤ 1 := fun k =>
    mul_inv_le_one_of_le₀ (ha k) hρpos.le
  have hx_nonneg : 0 ≤ x := hx ▸ Finset.prod_nonneg fun k _ => hfac_nonneg k
  have hx_le : ∀ j, x ≤ T.normalizedAbs (a j : F) * ρ⁻¹ := by
    intro j
    rw [hx, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact mul_le_of_le_one_right (hfac_nonneg j)
      (Finset.prod_le_one₀ (fun k _ => hfac_nonneg k) fun k _ => hfac_le k)
  have hx_le_one : x ≤ 1 := (hx_le 0).trans (hfac_le 0)
  -- The conjugating diagonal element `β_i = t ^ (n - i)`.
  let β : Fin (n + 1) → Fˣ := fun i => t ^ (n - i.val)
  have hβ : ∀ i j : Fin (n + 1), i ≤ j → β i * (β j)⁻¹ = t ^ (j.val - i.val) := by
    intro i j hij
    have hj := j.isLt
    have hij' : i.val ≤ j.val := hij
    have he : n - i.val = (n - j.val) + (j.val - i.val) := by omega
    simp only [β]
    rw [he, pow_add, mul_comm, inv_mul_cancel_left]
  -- The conjugate of every `u` in the set is integral.
  have hsub : {u : upperUnipotent (n + 1) F |
      u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L} ⊆
      diagonalConj β ⁻¹' (unipotentIntegralOpen F n :
        Set (upperUnipotent (n + 1) F)) := by
    intro u hu
    have hint : ∀ i j, T.normalizedAbs
        (((diagonalConj β u : upperUnipotent (n + 1) F) :
          GeneralLinear (n + 1) F).val i j) ≤ 1 := by
      intro i j
      rw [diagonalConj_entry, T.normalizedAbs_mul]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [hβ i j hij.le, normalizedAbs_units_pow]
        have hk : 1 ≤ j.val - i.val := by
          have : i.val < j.val := hij
          omega
        have h1 : x ^ (j.val - i.val) ≤ x := pow_le_of_le_one hx_nonneg hx_le_one (by omega)
        have h2 := hentry _ hu i j
        rw [hmul, T.normalizedAbs_mul] at h2
        calc x ^ (j.val - i.val) * T.normalizedAbs (u.val.val i j)
            ≤ T.normalizedAbs (a j : F) * ρ⁻¹ * T.normalizedAbs (u.val.val i j) :=
              mul_le_mul_of_nonneg_right (h1.trans (hx_le j)) (T.normalizedAbs_nonneg _)
          _ = T.normalizedAbs (u.val.val i j) * T.normalizedAbs (a j : F) * ρ⁻¹ := by
              ring
          _ ≤ 1 := mul_inv_le_one_of_le₀ (h2.trans hRρ) hρpos.le
      · rw [mul_inv_cancel, Units.val_one, T.normalizedAbs_one, one_mul,
          show u.val.val i i = 1 from UpperUnipotent.entry_diag u i, T.normalizedAbs_one]
      · rw [show u.val.val i j = 0 from UpperUnipotent.entry_eq_zero u hij,
          T.normalizedAbs_zero, mul_zero]
        exact zero_le_one
    show ((diagonalConj β u : upperUnipotent (n + 1) F) :
      GeneralLinear (n + 1) F) ∈ Conductor.levelSubgroup F n 0
    rw [Conductor.levelSubgroup_zero]
    exact Unramified.MinusculeCosets.unipotent_mem_integralSubgroup
      (diagonalConj β u).2 fun i j => (T.normalizedAbs_le_one_iff_mem_integers _).mp (hint i j)
  -- The volume of the integral conjugate.
  have hmeas : unipotentHaar F n (diagonalConj β ⁻¹' (unipotentIntegralOpen F n :
      Set (upperUnipotent (n + 1) F))) =
      (((T.leviModulus (GeneralLinear.BlockShape.singletons (n + 1))
        (GeneralLinear.BlockShape.singletonLevi F β) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    have hmap : (unipotentHaar F n).map (diagonalConj β) =
        ((T.leviModulus (GeneralLinear.BlockShape.singletons (n + 1))
          (GeneralLinear.BlockShape.singletonLevi F β) : ℝ≥0)⁻¹) •
          unipotentHaar F n := by
      obtain rfl : ‹MeasurableSpace (upperUnipotent (n + 1) F)› = borel _ :=
        BorelSpace.measurable_eq
      exact diagonalConj_map F T n β
    rw [← Measure.map_apply (continuous_diagonalConj β).measurable
      (unipotentIntegralOpen F n).isOpen.measurableSet, hmap,
      Measure.smul_apply, unipotentHaar_integral, ENNReal.smul_def, smul_eq_mul, mul_one]
  -- The modulus of `β` is `|t| ^ D`.
  have hmod : ((T.leviModulus (GeneralLinear.BlockShape.singletons (n + 1))
      (GeneralLinear.BlockShape.singletonLevi F β) : ℝ≥0) : ℝ) = x ^ D := by
    rw [singleton_modulus_real F T β]
    simp only [D, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.mp hj).2
    rw [div_eq_mul_inv, hβ i j hij.le, normalizedAbs_units_pow]
  have hxpos : 0 < x := T.normalizedAbs_pos t.ne_zero
  have hfinal : (x ^ D)⁻¹ = ρ ^ ((n + 1) * D) *
      ∏ i, (T.normalizedAbs (a i : F))⁻¹ ^ D := by
    rw [hx, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    simp only [mul_pow, mul_inv, inv_pow, inv_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, mul_comm D (n + 1), mul_comm]
  calc unipotentHaar F n
        {u | u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L}
      ≤ unipotentHaar F n (diagonalConj β ⁻¹' (unipotentIntegralOpen F n :
          Set (upperUnipotent (n + 1) F))) := measure_mono hsub
    _ = ENNReal.ofReal (ρ ^ ((n + 1) * D) *
          ∏ i, (T.normalizedAbs (a i : F))⁻¹ ^ D) := by
      rw [hmeas, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, hmod, hfinal]

end Langlands.AllField.RankinSelberg
