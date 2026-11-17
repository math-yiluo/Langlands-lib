import Langlands.Global.RankinSelberg.PaddedCuspWhittakerCompactTorusBound
import Langlands.Global.RankinSelberg.WhittakerCompactTorusIntegral

/-! # The padded Whittaker gauge bound for actual cuspidal realizations -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance padGaugeProofSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance padGaugeProofSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance padGaugeProofIdeleMeasurable (F : Type u) [Field F] [NumberField F] :
    MeasurableSpace (Ideles F) := borel _
local instance padGaugeProofIdeleBorel (F : Type u) [Field F] [NumberField F] :
    BorelSpace (Ideles F) := ⟨rfl⟩
local instance padGaugeProofIdeleLocallyCompact (F : Type u) [Field F] [NumberField F] :
    LocallyCompactSpace (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance padGaugeProofIdeleSecondCountable (F : Type u) [Field F] [NumberField F] :
    SecondCountableTopology (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

/-- The unchanged padded Whittaker gauge bound, over every number field and
for every actual cuspidal realization and proper padded block. -/
theorem unequalPadGauge : UnequalPadGaugeStatement.{u} := by
  intro F _ _ _ r t h T
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_cuspFunction_le F T
  let A : ℝ := 3 + ∑ j : Fin (t + 1),
    ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ)
  refine ⟨max 0 (A - β), le_max_left _ _, fun ψ hψ v σ hσ => ?_⟩
  have hσβ : A < β + σ := by
    linarith [le_max_right 0 (A - β)]
  let f := paddedCuspWhittakerNormWeight F h T ψ v σ
  change ∫⁻ p : WhittakerQuotient F (t + 1), f p.out
    ∂whittakerQuotientMeasure F (t + 1) < ⊤
  apply WhittakerCompactTorusIntegral.lintegral_whittakerQuotient_lt_top_of_compactTorusBound
    F (t + 1) (Measure.haar : Measure (Fin (t + 1) → Ideles F)) f
    (measurable_paddedCuspWhittakerNormWeight F h T ψ hψ v σ)
    (paddedCuspWhittakerNormWeight_unipotent_mul F h T ψ hψ v σ)
  intro C hC
  exact exists_padded_cusp_whittaker_compact_torus_bound F h T β hβ ψ hψ v
    Measure.haar σ hσβ hC

end Langlands.Global.RankinSelbergGlobal
