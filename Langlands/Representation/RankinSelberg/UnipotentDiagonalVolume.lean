import Langlands.Representation.RankinSelberg.DiagonalUnipotentHaar
import Langlands.Representation.Unramified.MinusculeCosets
import Langlands.LocalField.Normalization.Continuity
import Langlands.LocalField.Uniformizer
import Langlands.Representation.Whittaker.JPSDilationAssemblyProof

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

namespace Langlands.RankinSelberg

open GeneralLinear

universe uF

namespace UnipotentDiagonalVolume

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The normalized absolute value of a power of a unit. -/
theorem normalizedAbs_units_pow (T : F.TopologicalData) (x : F.Carrierˣ) (k : ℕ) :
    T.normalizedAbs ((x ^ k : F.Carrierˣ) : F.Carrier) =
      T.normalizedAbs (x : F.Carrier) ^ k := by
  rw [Units.val_pow_eq_pow_val]
  induction k with
  | zero => simp [T.normalizedAbs_one]
  | succ k ih => rw [pow_succ, T.normalizedAbs_mul, ih, pow_succ]

/-- The normalized absolute value of a product of units. -/
theorem normalizedAbs_units_prod (T : F.TopologicalData) {ι : Type*} (s : Finset ι)
    (x : ι → F.Carrierˣ) :
    T.normalizedAbs ((∏ k ∈ s, x k : F.Carrierˣ) : F.Carrier) =
      ∏ k ∈ s, T.normalizedAbs (x k : F.Carrier) := by
  rw [← T.normalizedAbsUnits_coe, map_prod, Units.coe_prod, NNReal.coe_prod]
  rfl

/-- Entries of a diagonal conjugate of a unipotent matrix. -/
theorem diagonalConj_entry {E : Type*} [Field E] {m : ℕ} (β : Fin m → Eˣ)
    (u : upperUnipotent m E) (i j : Fin m) :
    ((diagonalConj β u : upperUnipotent m E) : GeneralLinear m E).val i j =
      ((β i * (β j)⁻¹ : Eˣ) : E) * (u : GeneralLinear m E).val i j := by
  rw [diagonalConj_val, ← map_inv, Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val,
    Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, Matrix.diagonal_mul, Units.val_mul]
  simp only [Pi.inv_apply]
  ring

end UnipotentDiagonalVolume

open UnipotentDiagonalVolume

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance unipotentVolumeTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance unipotentVolumeValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance unipotentVolumeLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

variable {F}

/-- **Unipotent volume along a diagonal translate.** For a compact set `L` of
matrices there are a unit `r`, a constant `C` and exponents `e` such that, for
every diagonal `a`, if some `u · diag(a)` with `u` upper unipotent lies in `L`
then every `|a_i| ≤ |r|`, and the unipotent Haar volume of the `u` with
`u · diag(a) ∈ L` is at most `C ∏ |a_i|⁻¹ ^ e_i`. -/
theorem unipotentHaar_mul_diagonal_le (n : ℕ)
    [MeasurableSpace (upperUnipotent (n + 1) F.Carrier)]
    [BorelSpace (upperUnipotent (n + 1) F.Carrier)]
    (L : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (hL : IsCompact L) :
    ∃ (r : F.Carrierˣ) (C : ℝ) (e : Fin (n + 1) → ℕ), ∀ a : Fin (n + 1) → F.Carrierˣ,
      ((∃ u : upperUnipotent (n + 1) F.Carrier,
          u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L) →
        ∀ i, F.canonicalTopologicalData.normalizedAbs (a i : F.Carrier) ≤
          F.canonicalTopologicalData.normalizedAbs (r : F.Carrier)) ∧
      unipotentHaar F.Carrier n
          {u | u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L} ≤
        ENNReal.ofReal (C * ∏ i,
          (F.canonicalTopologicalData.normalizedAbs (a i : F.Carrier))⁻¹ ^ e i) := by
  set T := F.canonicalTopologicalData with hT
  -- A bound for the entries of the matrices in `L`.
  have hcont : Continuous fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier =>
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
  let r : F.Carrierˣ := LocalFactor.PadicAbelian.uniformizerUnit T ^ (-(m : ℤ))
  set ρ := T.normalizedAbs (r : F.Carrier) with hρdef
  have hρ : ρ = (T.residueCardinality : ℝ) ^ m := by
    rw [hρdef, LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs, neg_neg, zpow_natCast]
  have hρpos : 0 < ρ := T.normalizedAbs_pos r.ne_zero
  have hRρ : R ≤ ρ := hρ ▸ hm.le
  -- The exponent.
  let D : ℕ := ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
    (j.val - i.val)
  refine ⟨r, ρ ^ ((n + 1) * D), fun _ => D, fun a => ?_⟩
  -- Entries of `u · diag(a)`.
  have hmul : ∀ (u : upperUnipotent (n + 1) F.Carrier) (i j : Fin (n + 1)),
      (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier))) i j =
        u.val.val i j * (a j : F.Carrier) := fun u i j => Matrix.mul_diagonal _ _ _ _
  have hbound : (∃ u : upperUnipotent (n + 1) F.Carrier,
      u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L) →
      ∀ i, T.normalizedAbs (a i : F.Carrier) ≤ ρ := by
    rintro ⟨u, hu⟩ i
    have h := hentry _ hu i i
    rw [hmul, show u.val.val i i = 1 from UpperUnipotent.entry_diag u i, one_mul] at h
    exact h.trans hRρ
  refine ⟨hbound, ?_⟩
  by_cases hS : ∃ u : upperUnipotent (n + 1) F.Carrier,
      u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L
  swap
  · have hempty : {u : upperUnipotent (n + 1) F.Carrier |
        u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun u hu => hS ⟨u, hu⟩
    rw [hempty, measure_empty]
    exact zero_le
  have ha := hbound hS
  -- The contraction parameter `t = ∏ a_k / r`, with `|t| ≤ |a_j / r| ≤ 1`.
  let t : F.Carrierˣ := ∏ k, a k * r⁻¹
  set x := T.normalizedAbs (t : F.Carrier) with hxdef
  have hx : x = ∏ k, T.normalizedAbs (a k : F.Carrier) * ρ⁻¹ := by
    rw [hxdef, normalizedAbs_units_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_mul, T.normalizedAbs_mul, Langlands.Whittaker.JPSDilationAssembly.normalizedAbs_units_inv]
  have hfac_nonneg : ∀ k, 0 ≤ T.normalizedAbs (a k : F.Carrier) * ρ⁻¹ := fun k =>
    mul_nonneg (T.normalizedAbs_nonneg _) (inv_nonneg.mpr hρpos.le)
  have hfac_le : ∀ k, T.normalizedAbs (a k : F.Carrier) * ρ⁻¹ ≤ 1 := fun k =>
    mul_inv_le_one_of_le₀ (ha k) hρpos.le
  have hx_nonneg : 0 ≤ x := hx ▸ Finset.prod_nonneg fun k _ => hfac_nonneg k
  have hx_le : ∀ j, x ≤ T.normalizedAbs (a j : F.Carrier) * ρ⁻¹ := by
    intro j
    rw [hx, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact mul_le_of_le_one_right (hfac_nonneg j)
      (Finset.prod_le_one₀ (fun k _ => hfac_nonneg k) fun k _ => hfac_le k)
  have hx_le_one : x ≤ 1 := (hx_le 0).trans (hfac_le 0)
  -- The conjugating diagonal element `β_i = t ^ (n - i)`.
  let β : Fin (n + 1) → F.Carrierˣ := fun i => t ^ (n - i.val)
  have hβ : ∀ i j : Fin (n + 1), i ≤ j → β i * (β j)⁻¹ = t ^ (j.val - i.val) := by
    intro i j hij
    have hj := j.isLt
    have hij' : i.val ≤ j.val := hij
    have he : n - i.val = (n - j.val) + (j.val - i.val) := by omega
    simp only [β]
    rw [he, pow_add, mul_comm, inv_mul_cancel_left]
  -- The conjugate of every `u` in the set is integral.
  have hsub : {u : upperUnipotent (n + 1) F.Carrier |
      u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L} ⊆
      diagonalConj β ⁻¹' (unipotentIntegralOpen F.Carrier n :
        Set (upperUnipotent (n + 1) F.Carrier)) := by
    intro u hu
    have hint : ∀ i j, T.normalizedAbs
        (((diagonalConj β u : upperUnipotent (n + 1) F.Carrier) :
          GeneralLinear (n + 1) F.Carrier).val i j) ≤ 1 := by
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
            ≤ T.normalizedAbs (a j : F.Carrier) * ρ⁻¹ * T.normalizedAbs (u.val.val i j) :=
              mul_le_mul_of_nonneg_right (h1.trans (hx_le j)) (T.normalizedAbs_nonneg _)
          _ = T.normalizedAbs (u.val.val i j) * T.normalizedAbs (a j : F.Carrier) * ρ⁻¹ := by
              ring
          _ ≤ 1 := mul_inv_le_one_of_le₀ (h2.trans hRρ) hρpos.le
      · rw [mul_inv_cancel, Units.val_one, T.normalizedAbs_one, one_mul,
          show u.val.val i i = 1 from UpperUnipotent.entry_diag u i, T.normalizedAbs_one]
      · rw [show u.val.val i j = 0 from UpperUnipotent.entry_eq_zero u hij,
          T.normalizedAbs_zero, mul_zero]
        exact zero_le_one
    show ((diagonalConj β u : upperUnipotent (n + 1) F.Carrier) :
      GeneralLinear (n + 1) F.Carrier) ∈ Conductor.levelSubgroup F.Carrier n 0
    rw [Conductor.levelSubgroup_zero]
    exact Unramified.MinusculeCosets.unipotent_mem_integralSubgroup
      (diagonalConj β u).2 fun i j => (T.normalizedAbs_le_one_iff_mem_integers _).mp (hint i j)
  -- The volume of the integral conjugate.
  have hmeas : unipotentHaar F.Carrier n (diagonalConj β ⁻¹' (unipotentIntegralOpen F.Carrier n :
      Set (upperUnipotent (n + 1) F.Carrier))) =
      (((T.leviModulus (GeneralLinear.BlockShape.singletons (n + 1))
        (GeneralLinear.BlockShape.singletonLevi F.Carrier β) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    have hmap : (unipotentHaar F.Carrier n).map (diagonalConj β) =
        ((T.leviModulus (GeneralLinear.BlockShape.singletons (n + 1))
          (GeneralLinear.BlockShape.singletonLevi F.Carrier β) : ℝ≥0)⁻¹) •
          unipotentHaar F.Carrier n := by
      obtain rfl : ‹MeasurableSpace (upperUnipotent (n + 1) F.Carrier)› = borel _ :=
        BorelSpace.measurable_eq
      exact diagonalConj_map F T n β
    rw [← Measure.map_apply (continuous_diagonalConj β).measurable
      (unipotentIntegralOpen F.Carrier n).isOpen.measurableSet, hmap,
      Measure.smul_apply, unipotentHaar_integral, ENNReal.smul_def, smul_eq_mul, mul_one]
  -- The modulus of `β` is `|t| ^ D`.
  have hmod : ((T.leviModulus (GeneralLinear.BlockShape.singletons (n + 1))
      (GeneralLinear.BlockShape.singletonLevi F.Carrier β) : ℝ≥0) : ℝ) = x ^ D := by
    rw [singleton_modulus_real F T β]
    simp only [D, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.mp hj).2
    rw [div_eq_mul_inv, hβ i j hij.le, normalizedAbs_units_pow]
  have hxpos : 0 < x := T.normalizedAbs_pos t.ne_zero
  have hfinal : (x ^ D)⁻¹ = ρ ^ ((n + 1) * D) *
      ∏ i, (T.normalizedAbs (a i : F.Carrier))⁻¹ ^ D := by
    rw [hx, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    simp only [mul_pow, mul_inv, inv_pow, inv_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, mul_comm D (n + 1), mul_comm]
  calc unipotentHaar F.Carrier n
        {u | u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L}
      ≤ unipotentHaar F.Carrier n (diagonalConj β ⁻¹' (unipotentIntegralOpen F.Carrier n :
          Set (upperUnipotent (n + 1) F.Carrier))) := measure_mono hsub
    _ = ENNReal.ofReal (ρ ^ ((n + 1) * D) *
          ∏ i, (T.normalizedAbs (a i : F.Carrier))⁻¹ ^ D) := by
      rw [hmeas, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, hmod, hfinal]

end Langlands.RankinSelberg
