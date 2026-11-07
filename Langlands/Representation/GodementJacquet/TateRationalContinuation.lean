import Langlands.Representation.GodementJacquet.TateAdditiveMellin
import Langlands.Representation.GodementJacquet.TateCharacterDenominator
import Langlands.LocalFactor.Abelian.ZetaLaurentFormula
import Mathlib.Analysis.Analytic.Polynomial

/-! Actual rational Mellin continuations and normal meromorphic Tate continuations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Topology

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg Filter

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
private local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩
private local instance : MeasurableSpace F.Carrierˣ := borel _
private local instance : BorelSpace F.Carrierˣ := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "q" => F.canonicalTopologicalData.residueCardinality

/-- The principal-power and exponential spectral conventions agree. -/
theorem tate_spectralPoint_eq (s : ℂ) :
    spectralPoint q s = LocalFactor.PadicAbelian.spectralVariable T s := by
  rw [spectralPoint, Complex.cpow_def_of_ne_zero
    (by exact_mod_cast (Nat.zero_lt_one.trans
      F.canonicalTopologicalData.residueCardinality_gt_one).ne')]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log
    (show (0 : ℝ) ≤ (q : ℝ) by positivity)]
  exact congrArg Complex.exp (mul_comm _ _)

private theorem analyticAt_tate_spectralPoint (s : ℂ) :
    AnalyticAt ℂ (spectralPoint q) s := by
  rw [funext (tate_spectralPoint_eq F)]
  unfold LocalFactor.PadicAbelian.spectralVariable
  fun_prop

/-- Rational evaluation is analytic whenever its reduced denominator is nonzero. -/
theorem analyticAt_tate_rationalEval (R : RationalFunctions) (s : ℂ)
    (hR : R.denom.eval (spectralPoint q s) ≠ 0) :
    AnalyticAt ℂ
      (fun z => RatFunc.eval (RingHom.id ℂ) (spectralPoint q z) R) s := by
  simp only [RatFunc.eval, Polynomial.eval₂_id]
  apply AnalyticAt.div
  · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      using (analyticAt_tate_spectralPoint F s).aeval_polynomial R.num
  · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      using (analyticAt_tate_spectralPoint F s).aeval_polynomial R.denom
  · exact hR

/-- The raw rational evaluation is meromorphic even at its excluded poles. -/
theorem meromorphicOn_tate_rationalEval (R : RationalFunctions) :
    MeromorphicOn
      (fun z => RatFunc.eval (RingHom.id ℂ) (spectralPoint q z) R) Set.univ := by
  intro s _
  simp only [RatFunc.eval, Polynomial.eval₂_id]
  apply MeromorphicAt.div
  · have h : AnalyticAt ℂ (fun z => R.num.eval (spectralPoint q z)) s := by
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
        using (analyticAt_tate_spectralPoint F s).aeval_polynomial R.num
    exact h.meromorphicAt
  · have h : AnalyticAt ℂ (fun z => R.denom.eval (spectralPoint q z)) s := by
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
        using (analyticAt_tate_spectralPoint F s).aeval_polynomial R.denom
    exact h.meromorphicAt

private theorem tate_convergesAt_on_right (π : F.Carrierˣ)
    (χ : Quasicharacter F.Carrier) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      LocalFactor.PadicAbelian.ConvergesAt T π χ s := by
  have hχ : 0 < ‖(χ π : ℂ)‖ := norm_pos_iff.mpr (χ π).ne_zero
  obtain ⟨b, hb⟩ := character_spectral_threshold
    F.canonicalTopologicalData.residueCardinality_gt_one (one_div_pos.mpr hχ)
  refine ⟨b, fun s hs => ?_⟩
  rw [LocalFactor.PadicAbelian.convergesAt_iff_norm_lt_one, norm_mul,
    ← tate_spectralPoint_eq F]
  have h := (lt_div_iff₀ hχ).mp (hb s hs)
  simpa only [mul_comm] using h

/-- Every actual rational scalar continuation agrees, with the exact Haar mass,
with every supplied additive continuation on every punctured neighbourhood. -/
theorem scalarRationalContinuation_eq_additiveGerm
    (ν : AdditiveHaarMeasure F.Carrier) (π : F.Carrierˣ)
    (χ : Quasicharacter F.Carrier) (Φ : SchwartzBruhat F.Carrier)
    (R : RationalFunctions)
    (hR : HasRationalContinuation q
      (scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
        (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1 Φ) R)
    (Z : ℂ → ℂ)
    (hZ : LocalFactor.PadicAbelian.ExtendsIntegral T π ν.measure Φ χ Z)
    (t : ℂ) :
    (fun s => ((ν.measure (LocalFactor.PadicAbelian.integralUnits T)).toReal : ℂ) *
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) =ᶠ[𝓝[≠] t] Z := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := tate_convergesAt_on_right F π χ
  let s₀ : ℂ := ((max a b + 1 : ℝ) : ℂ)
  have hlocal :
      (fun s => ((ν.measure (LocalFactor.PadicAbelian.integralUnits T)).toReal : ℂ) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) =ᶠ[𝓝 s₀] Z := by
    have hn : {s : ℂ | max a b < s.re} ∈ 𝓝 s₀ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        dsimp [s₀]
        simp)
    filter_upwards [hn] with s hs
    rw [hZ.2 s (hb s ((le_max_right a b).trans_lt hs)),
      ← (ha s ((le_max_left a b).trans_lt hs)).2,
      scalarMellinIntegral_eq_zeta F ν χ Φ s, ← mul_assoc]
    have hm :
        ((ν.measure (LocalFactor.PadicAbelian.integralUnits T)).toReal : ℂ) ≠ 0 := by
      exact_mod_cast (tate_integralUnits_mass_pos F ν).ne'
    rw [mul_inv_cancel₀ hm, one_mul]
  exact LocalFactor.PadicAbelian.meromorphic_germ_eq_of_eventuallyEq
    (fun s _ => analyticAt_const.meromorphicAt.mul
      (meromorphicOn_tate_rationalEval F R s (Set.mem_univ s)))
    hZ.1.meromorphicOn hlocal t

/-- A unique genuine additive continuation accompanies every rational Mellin
continuation, with the normalization visible in every punctured germ. -/
def TateRationalContinuationComparisonStatement : Prop :=
  ∀ (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat F.Carrier) (R : RationalFunctions),
    HasRationalContinuation q
      (scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
        (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1 Φ) R →
    ∃! Z : ℂ → ℂ,
      LocalFactor.PadicAbelian.ExtendsIntegral T
        (LocalFactor.PadicAbelian.uniformizerUnit T) ν.measure Φ χ Z ∧
      ∀ t : ℂ,
        (fun s => ((ν.measure (LocalFactor.PadicAbelian.integralUnits T)).toReal : ℂ) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) =ᶠ[𝓝[≠] t] Z

theorem tateRationalContinuationComparisonStatement :
    TateRationalContinuationComparisonStatement F := by
  intro ν χ Φ R hR
  obtain ⟨Z, hZ, _⟩ := (LocalFactor.PadicAbelian.zeta_analysis T
    (LocalFactor.PadicAbelian.uniformizerUnit T)
    (LocalFactor.PadicAbelian.uniformizerUnit_ord T) χ
    (F.canonicalTopologicalData.multiplicativeConductor χ)
    ((LocalFactor.PadicAbelian.conductorAt_iff T χ _).mpr rfl) ν Φ).2.2.1
  refine ⟨Z, ⟨hZ, fun t =>
    scalarRationalContinuation_eq_additiveGerm F ν _ χ Φ R hR Z hZ t⟩, ?_⟩
  intro Y hY
  exact LocalFactor.PadicAbelian.extendsIntegral_unique T _ ν.measure Φ χ hY.1 hZ

end Langlands.GodementJacquet.Padic
