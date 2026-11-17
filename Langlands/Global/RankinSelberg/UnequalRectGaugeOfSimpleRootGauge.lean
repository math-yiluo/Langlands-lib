import Langlands.Global.RankinSelberg.DualWhittakerGaugeReduction
import Langlands.Global.RankinSelberg.RectangularGaugeReductionProof

/-! # Conditional assembly of the unequal-rank rectangular gauge bound -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The two shared analytic gauge inputs imply the unchanged rectangular
Whittaker gauge proposition, for every number field and every proper block. -/
theorem unequalRectGauge_of_simpleRootGauge
    (hmajorization : WhittakerSimpleRootMajorizationStatement.{u})
    (hMellin : AdelicSimpleRootGaugeRectangularMellinStatement.{u}) :
    UnequalRectGaugeStatement.{u} := by
  intro F _ _ _ r t h T
  obtain ⟨β, τ, hτ, hmajor⟩ :=
    translatedDualCuspWhittaker_majorization_of_simpleRoot F T h hmajorization
  exact rectWhittakerGaugeBound_of_simpleRootGauge F h T β τ hτ hmajor hMellin

end Langlands.Global.RankinSelbergGlobal
