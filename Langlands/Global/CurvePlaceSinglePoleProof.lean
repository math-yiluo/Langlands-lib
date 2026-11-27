import Langlands.Global.CurvePlaceSinglePoleStatement
import Langlands.Global.CurveChartAdditiveQuotient
import Langlands.Global.DedekindAwaySInteger
import Langlands.Global.FiniteConstantChartPrimeGenerator
import Langlands.Global.FunctionFieldValuationPlaces

/-! # A parameter with a pole only at the specified curve place -/

noncomputable section

universe u

open AlgebraicCurve IntermediateField IsDedekindDomain
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global.FiniteConstantCurveChart

namespace Langlands.Global

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

set_option maxHeartbeats 1000000 in
/-- The function field contains a function with a pole at the given actual place
and integral at every other actual place. -/
theorem exists_curvePlace_singlePole (v : Place k F) :
    ∃ f : F, f ∉ v.toValuationSubring ∧ ∀ w : Place k F, w ≠ v → f ∈ w.toValuationSubring := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : F, s ∉ v.toValuationSubring := by
    by_contra! h
    exact v.ne_top' (top_unique (fun x _ => h x))
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.toValuationSubring.zero_mem)
  have hsval : 1 < v.adicValuation s := lt_of_not_ge (fun h => hs (v.mem_iff_adicValuation_le_one.mpr h))
  have ht : Transcendental k s := Valuation.transcendental_of_ne_one k s hs0 hsval.ne'
  have hi : Transcendental k s⁻¹ := Valuation.transcendental_of_ne_one k s⁻¹ (inv_ne_zero hs0)
    ((v.adicValuation.one_lt_val_iff hs0).mp hsval).ne
  let : FiniteDimensional k⟮s⟯ F := FunctionField.finiteDimensional_of_adjoin_transcendental ht
  let : FiniteDimensional k⟮s⁻¹⟯ F := FunctionField.finiteDimensional_of_adjoin_transcendental hi
  let C := CurveModel.chartRing k ({s⁻¹} : Set F)
  let D := CurveModel.chartRing k ({s, s⁻¹} : Set F)
  have hsi : s⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem s).resolve_left hs
  let P := CurveModel.primeOfValuationSubring k s⁻¹ v.toValuationSubring v.algebraMap_mem' hsi v.ne_top'
  let z := CurveModel.tInvChart k s
  have hz0 : z ≠ 0 := fun h => (inv_ne_zero hs0) (congrArg (fun c : C => (c : F)) h)
  have hzP : z ∈ P.asIdeal := by
    change v.toValuationSubring.valuation s⁻¹ < 1
    exact (v.toValuationSubring.valuation.one_lt_val_iff hs0).mp (lt_of_not_ge (fun h => hs ((v.toValuationSubring.valuation_le_one_iff _).mp h)))
  let : Finite (ClassGroup C) := finite_classGroup_normalizedCurveChart k F s⁻¹ hi
  obtain ⟨d, hd0, hdP, hdQ⟩ := exists_primePowerGenerator C P
  let x := (d : F)⁻¹
  have hxD : x ∈ D := by
    have hxloc : x ∈ dedekindAwaySubalgebra (K := F) z hz0 := by
      apply (mem_dedekindAwaySubalgebra_iff z hz0 x).mpr
      intro Q hzQ
      have hne : Q ≠ P := fun h => hzQ (h ▸ hzP)
      change Q.valuation F ((algebraMap C F d)⁻¹) ≤ 1
      rw [map_inv₀, (Q.valuation_eq_one_iff_notMem).mpr (hdQ Q hne), inv_one]
    obtain ⟨a, b, hb, hx⟩ := hxloc
    obtain ⟨n, rfl⟩ := hb
    rw [hx, map_pow, ← inv_pow]
    change (a : F) * ((s⁻¹)⁻¹)^n ∈ D
    rw [inv_inv]
    exact D.mul_mem (CurveModel.inclInf k s a).property
      (D.pow_mem (CurveModel.subset_chartRing k _ (by simp)) n)
  have hdx0 : (d : F) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hxv : 1 < v.toValuationSubring.valuation x :=
    (v.toValuationSubring.valuation.val_lt_one_iff hdx0).mp hdP
  have hxw (w : Place k F) (hw : w ≠ v) (hwi : s⁻¹ ∈ w.toValuationSubring) :
      x ∈ w.toValuationSubring := by
    let Q := CurveModel.primeOfValuationSubring k s⁻¹ w.toValuationSubring w.algebraMap_mem' hwi w.ne_top'
    have hne : Q ≠ P := fun h => hw (by
      rw [← FiniteConstantCurveChart.ofHeightOneSpectrum_center k F s⁻¹ w hwi,
        ← FiniteConstantCurveChart.ofHeightOneSpectrum_center k F s⁻¹ v hsi]
      exact congrArg (Place.ofHeightOneSpectrum (K := k)) h)
    have hval := CurveModel.valuation_eq_one_of_not_mem_centre k s⁻¹
      w.toValuationSubring w.algebraMap_mem' hwi (hdQ Q hne)
    apply (w.toValuationSubring.valuation_le_one_iff _).mp
    change w.toValuationSubring.valuation ((d : F)⁻¹) ≤ 1
    rw [map_inv₀, hval, inv_one]
  let W := curveChartSum k F s
  let q := W.mkQ
  let powers (n : ℕ) : curveChartAdditiveQuotient k F s :=
    ⟨q (x^n), Submodule.mem_map.mpr ⟨x^n, D.pow_mem hxD n, rfl⟩⟩
  let : Finite (curveChartAdditiveQuotient k F s) := finite_curveChartAdditiveQuotient k F s hs0
  obtain ⟨i, j, hij, hsame⟩ := Finite.exists_ne_map_eq_of_infinite powers
  have hval_ne : v.toValuationSubring.valuation (x^i) ≠ v.toValuationSubring.valuation (x^j) := by
    rw [map_pow, map_pow]
    exact fun h => hij (pow_right_injective₀ (zero_lt_one.trans hxv) hxv.ne' h)
  have hpole : x^i - x^j ∉ v.toValuationSubring := by
    rw [← v.toValuationSubring.valuation_le_one_iff]
    have hge (n : ℕ) : 1 ≤ v.toValuationSubring.valuation (x^n) := by
      rw [map_pow]
      exact one_le_pow₀ hxv.le
    rcases lt_or_gt_of_ne hval_ne with h | h
    · rw [v.toValuationSubring.valuation.map_sub_eq_of_lt_right h, map_pow]
      exact not_le.mpr (one_lt_pow₀ hxv (fun hj => (not_lt_of_ge (hge i)) (by simpa [hj] using h)))
    · rw [v.toValuationSubring.valuation.map_sub_eq_of_lt_left h, map_pow]
      exact not_le.mpr (one_lt_pow₀ hxv (fun hi => (not_lt_of_ge (hge j)) (by simpa [hi] using h)))
  have hq : q (x^i - x^j) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun t : curveChartAdditiveQuotient k F s => t.val) hsame
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Submodule.Quotient.mk_eq_zero W).mp hq)
  refine ⟨a, ?_, ?_⟩
  · intro ha'
    apply hpole
    rw [← hab]
    exact v.toValuationSubring.toSubring.add_mem ha'
      (CurveModel.chartRing_le_valuationSubring v.toValuationSubring
        v.algebraMap_mem' (Set.singleton_subset_iff.mpr hsi) hb)
  · intro w hw
    by_cases hs' : s ∈ w.toValuationSubring
    · exact CurveModel.chartRing_le_valuationSubring w.toValuationSubring
        w.algebraMap_mem' (Set.singleton_subset_iff.mpr hs') ha
    · have hsi' := (w.toValuationSubring.mem_or_inv_mem s).resolve_left hs'
      have hb' := CurveModel.chartRing_le_valuationSubring w.toValuationSubring
        w.algebraMap_mem' (Set.singleton_subset_iff.mpr hsi') hb
      have hd' := w.toValuationSubring.toSubring.sub_mem
        (w.toValuationSubring.pow_mem (hxw w hw hsi') i)
        (w.toValuationSubring.pow_mem (hxw w hw hsi') j)
      rw [← hab] at hd'
      simpa using w.toValuationSubring.toSubring.sub_mem hd' hb'

theorem curvePlaceSinglePole : CurvePlaceSinglePoleStatement.{u} := by
  intro k F _ _ _ _ _ _ _ v
  exact exists_curvePlace_singlePole k F v

end Langlands.Global
