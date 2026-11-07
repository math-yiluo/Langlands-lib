import Langlands.Representation.GodementJacquet.TateRationalContinuation
import Langlands.LocalFactor.Abelian.TateFunctionalEquation

/-! The concrete Gauss coefficient in the actual rational scalar functional equation. -/

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

private theorem tate_polynomial_analytic (P : Polynomial ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun z => P.eval (spectralPoint q z)) s := by
  have h : AnalyticAt ℂ (spectralPoint q) s := by
    rw [funext (tate_spectralPoint_eq F)]
    unfold LocalFactor.PadicAbelian.spectralVariable
    fun_prop
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    using h.aeval_polynomial P

private theorem tate_one_sub_tendsto (s : ℂ) :
    Tendsto (fun z : ℂ => 1 - z) (𝓝[≠] s) (𝓝[≠] (1 - s)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact fun h => hz (sub_right_injective h)

/-- Multiplication by the actual Euler polynomial is division by the abelian
Euler expression, including its totalized values. -/
theorem tate_lPolynomial_eval_eq_lFactorAt_inv
    (χ : Quasicharacter F.Carrier) (s : ℂ) :
    (LocalFactor.PadicAbelian.lPolynomial T χ).eval (spectralPoint q s) =
      (LocalFactor.PadicAbelian.lFactorAt T
        (LocalFactor.PadicAbelian.uniformizerUnit T) χ
        (F.canonicalTopologicalData.multiplicativeConductor χ) s)⁻¹ := by
  classical
  rw [LocalFactor.PadicAbelian.lFactorAt_inv_eq, tate_spectralPoint_eq F]
  by_cases h : F.canonicalTopologicalData.multiplicativeConductor χ = 0 <;>
    simp [LocalFactor.PadicAbelian.lPolynomial, h]

/-- Actual Fourier tests give the concrete Gauss equation for every pair of
rational scalar Mellin continuations, at every point where both are regular. -/
def TateRationalGaussFunctionalEquationStatement : Prop :=
  ∀ (ν : AdditiveHaarMeasure F.Carrier) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (χ : Quasicharacter F.Carrier) (Φ : SchwartzBruhat F.Carrier),
    ∃ Φhat : SchwartzBruhat F.Carrier,
      (∀ y, Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
        Φhat y = fourierIntegral ψ ν Φ y) ∧
      ∀ R RDual : RationalFunctions,
        HasRationalContinuation q
          (scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
            (localMultiplicativeHaar F.Carrier) (fun x => (χ x : ℂ)) 1 Φ) R →
        HasRationalContinuation q
          (scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
            (localMultiplicativeHaar F.Carrier) (fun x => (χ⁻¹ x : ℂ)) 1 Φhat) RDual →
        ∀ s : ℂ,
          R.denom.eval (spectralPoint q s) ≠ 0 →
          RDual.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
          (LocalFactor.PadicAbelian.lPolynomial T χ⁻¹).eval
              (spectralPoint q (1 - s)) *
            RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) RDual =
          LocalFactor.PadicAbelian.epsilon T χ ψ ν.measure s *
            ((LocalFactor.PadicAbelian.lPolynomial T χ).eval (spectralPoint q s) *
              RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R)

theorem tateRationalGaussFunctionalEquationStatement :
    TateRationalGaussFunctionalEquationStatement F := by
  intro ν ψ χ Φ
  let π := LocalFactor.PadicAbelian.uniformizerUnit T
  let a := F.canonicalTopologicalData.multiplicativeConductor χ
  let n := F.canonicalTopologicalData.additiveConductor ψ
  have hπ : F.canonicalTopologicalData.ord (π : F.Carrier) = 1 :=
    LocalFactor.PadicAbelian.uniformizerUnit_ord T
  have hχ : LocalFactor.PadicAbelian.ConductorAt T χ a :=
    (LocalFactor.PadicAbelian.conductorAt_iff T χ a).mpr rfl
  have hψ : LocalFactor.PadicAbelian.AdditiveConductorAt T ψ.toAddChar n :=
    (LocalFactor.PadicAbelian.additiveConductorAt_iff T ψ n).mpr rfl
  have hχinv : F.canonicalTopologicalData.multiplicativeConductor χ⁻¹ = a :=
    ((LocalFactor.PadicAbelian.conductorAt_iff T χ⁻¹ a).mp
      (LocalFactor.PadicAbelian.conductorAt_inv T χ a hχ)).symm
  obtain ⟨Φhat, hΦhat, hFE⟩ :=
    LocalFactor.PadicAbelian.fourier_functional_equation T π hπ χ hχ ψ hψ ν Φ
  refine ⟨Φhat, fun y => ⟨fourierIntegrand_integrable ψ ν Φ y, hΦhat y⟩, ?_⟩
  intro R RDual hR hRDual s hRs hRDuals
  obtain ⟨Z, hZ, _⟩ := tateRationalContinuationComparisonStatement F ν χ Φ R hR
  obtain ⟨Y, hY, _⟩ :=
    tateRationalContinuationComparisonStatement F ν χ⁻¹ Φhat RDual hRDual
  let m : ℂ := ((ν.measure (LocalFactor.PadicAbelian.integralUnits T)).toReal : ℂ)
  have hm : m ≠ 0 := by
    dsimp only [m]
    exact_mod_cast (tate_integralUnits_mass_pos F ν).ne'
  have hG :
      (fun z => (LocalFactor.PadicAbelian.lPolynomial T χ⁻¹).eval
          (spectralPoint q (1 - z)) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - z)) RDual) =ᶠ[𝓝[≠] s]
      (fun z => LocalFactor.PadicAbelian.epsilon T χ ψ ν.measure z *
        ((LocalFactor.PadicAbelian.lPolynomial T χ).eval (spectralPoint q z) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q z) R)) := by
    filter_upwards [hFE Z Y hZ.1 hY.1 s, hZ.2 s,
      (hY.2 (1 - s)).comp_tendsto (tate_one_sub_tendsto s)] with z hfe hz hy
    dsimp only [Function.comp_def] at hy
    have hP := tate_lPolynomial_eval_eq_lFactorAt_inv F χ z
    have hPDual := tate_lPolynomial_eval_eq_lFactorAt_inv F χ⁻¹ (1 - z)
    rw [hχinv] at hPDual
    rw [← hz, ← hy, div_eq_mul_inv, div_eq_mul_inv, ← hP, ← hPDual] at hfe
    change (m * RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - z)) RDual) *
        (LocalFactor.PadicAbelian.lPolynomial T χ⁻¹).eval
          (spectralPoint q (1 - z)) =
      LocalFactor.PadicAbelian.epsilon T χ ψ ν.measure z *
        ((m * RatFunc.eval (RingHom.id ℂ) (spectralPoint q z) R) *
          (LocalFactor.PadicAbelian.lPolynomial T χ).eval (spectralPoint q z)) at hfe
    apply mul_left_cancel₀ hm
    calc
      m * ((LocalFactor.PadicAbelian.lPolynomial T χ⁻¹).eval
          (spectralPoint q (1 - z)) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - z)) RDual) =
        (m * RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - z)) RDual) *
          (LocalFactor.PadicAbelian.lPolynomial T χ⁻¹).eval
            (spectralPoint q (1 - z)) := by ring
      _ = _ := hfe
      _ = _ := by ring
  have han : AnalyticAt ℂ (fun z : ℂ => 1 - z) s :=
    analyticAt_const.sub analyticAt_id
  have hLeft : AnalyticAt ℂ
      (fun z => (LocalFactor.PadicAbelian.lPolynomial T χ⁻¹).eval
          (spectralPoint q (1 - z)) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - z)) RDual) s :=
    ((tate_polynomial_analytic F _ (1 - s)).mul
      (analyticAt_tate_rationalEval F RDual (1 - s) hRDuals)).comp han
  have hε : AnalyticAt ℂ (LocalFactor.PadicAbelian.epsilon T χ ψ ν.measure) s := by
    change AnalyticAt ℂ
      (LocalFactor.PadicAbelian.epsilonAt T π χ ψ.toAddChar ν.measure a n) s
    exact (LocalFactor.PadicAbelian.epsilonAt_differentiable T π χ ψ.toAddChar
      ν.measure a n).analyticAt s
  have hRight : AnalyticAt ℂ
      (fun z => LocalFactor.PadicAbelian.epsilon T χ ψ ν.measure z *
        ((LocalFactor.PadicAbelian.lPolynomial T χ).eval (spectralPoint q z) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q z) R)) s :=
    hε.mul ((tate_polynomial_analytic F _ s).mul
      (analyticAt_tate_rationalEval F R s hRs))
  exact ((hLeft.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    hRight.meromorphicNFAt).mp hG).eq_of_nhds

end Langlands.GodementJacquet.Padic
