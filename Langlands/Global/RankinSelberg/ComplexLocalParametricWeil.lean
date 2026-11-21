import Langlands.Analysis.Local.QuotientWeilKernel
import Langlands.Global.RankinSelberg.ComplexLocalIwasawa

/-! # Integrable orbital averages with an independent parameter -/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa

open ArchimedeanLocal
open ComplexLocalWhittakerGauge (logTorus)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ

/-- The positive triangular and unitary coordinates give a continuous section of the
complex unipotent quotient. -/
def quotientRepresentative (q : Q) : G :=
  logTorus ((quotientHomeomorph (r + 1) q).1) * (quotientHomeomorph (r + 1) q).2.val

theorem continuous_quotientRepresentative : Continuous (quotientRepresentative (r := r)) :=
  (continuous_logTorus.comp (continuous_fst.comp (quotientHomeomorph (r + 1)).continuous)).mul
    (continuous_subtype_val.comp (continuous_snd.comp (quotientHomeomorph (r + 1)).continuous))

theorem mk_quotientRepresentative (q : Q) :
    Quotient.mk _ (quotientRepresentative q) = q :=
  (quotientHomeomorph (r + 1)).symm_apply_apply q

local instance parametricWeilGroupSecondCountable : SecondCountableTopology G :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance parametricWeilUnipotentSecondCountable : SecondCountableTopology N :=
  Topology.IsInducing.subtypeVal.secondCountableTopology
local instance parametricWeilUnipotentLocallyCompact : LocallyCompactSpace N :=
  GeneralLinear.UpperUnipotent.locallyCompactSpace

private theorem lintegral_orbit_representative (D : ComplexQuotientMeasureData r)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q : Q, ∫⁻ u : N, F (u.val * quotientRepresentative q) ∂D.unipotentHaar ∂D.measure) =
      ∫⁻ g, F g ∂D.groupHaar := by
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let hN : IsClosed (N : Set G) := GeneralLinear.UpperUnipotent.isClosed
  rw [← lintegral_orbitKernel N hN D.unipotentHaar D.groupHaar D.measure D.compatible F hF]
  refine lintegral_congr fun q => ?_
  have hq : orbitKernel N hN D.unipotentHaar q =
      Measure.map (fun u : N => u.val * quotientRepresentative q) D.unipotentHaar := by
    conv_lhs => rw [← mk_quotientRepresentative q]
    exact orbitKernel_mk N hN D.unipotentHaar (quotientRepresentative q)
  rw [hq, lintegral_map hF (continuous_subtype_val.mul_const _).measurable]

/-- Absolute integrability of a parametrized group kernel implies absolute
integrability of its orbital averages on the quotient times the parameter space. -/
def ComplexLocalParametricWeilStatement : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (ρ : Measure X) [SFinite ρ]
    (D : ComplexQuotientMeasureData r) (F : X × G → ℂ), Measurable F →
    Integrable F (ρ.prod D.groupHaar) →
    Integrable (fun p : Q × X => ∫ u : N, F (p.2, u.val * quotientRepresentative p.1)
      ∂D.unipotentHaar) (D.measure.prod ρ)

theorem complexLocalParametricWeil : ComplexLocalParametricWeilStatement (r := r) := by
  intro X _ ρ _ D F hF hInt
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaCompactSpace Q := (quotientHomeomorph (r + 1)).isClosedEmbedding.sigmaCompactSpace
  let : D.measure.Regular := D.compatible.regular
  let : SigmaFinite D.measure := inferInstance
  let A (p : (Q × X) × N) := F (p.1.2, p.2.val * quotientRepresentative p.1.1)
  have hA : Measurable A := hF.comp (measurable_fst.snd.prodMk
    ((continuous_subtype_val.measurable.comp measurable_snd).mul
      (continuous_quotientRepresentative.measurable.comp measurable_fst.fst)))
  let B (p : Q × X) := ∫ u : N, A (p, u) ∂D.unipotentHaar
  have hB : StronglyMeasurable B := hA.stronglyMeasurable.integral_prod_right'
  refine ⟨hB.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm' _ hB.enorm]
  change (∫⁻ x, ∫⁻ q, ‖B (q, x)‖ₑ ∂D.measure ∂ρ) < ⊤
  calc
    _ ≤ ∫⁻ x, ∫⁻ q : Q, ∫⁻ u : N, ‖F (x, u.val * quotientRepresentative q)‖ₑ
        ∂D.unipotentHaar ∂D.measure ∂ρ :=
      lintegral_mono fun x => lintegral_mono fun q => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x, ∫⁻ g, ‖F (x, g)‖ₑ ∂D.groupHaar ∂ρ := by
      refine lintegral_congr fun x => ?_
      exact lintegral_orbit_representative D (fun g => ‖F (x, g)‖ₑ)
        (hF.enorm.comp measurable_prodMk_left)
    _ = ∫⁻ p, ‖F p‖ₑ ∂ρ.prod D.groupHaar := (lintegral_prod _ hF.enorm.aemeasurable).symm
    _ < ⊤ := hInt.hasFiniteIntegral

end Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa
