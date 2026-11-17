import Langlands.Global.RankinSelberg.WhittakerSchwartzGaugeReduction
import Langlands.Global.RankinSelberg.WhittakerSimpleRootMajorization
import Langlands.Global.RankinSelberg.AdelicGaugeSchwartzTorusMellin

/-! # The uniform weighted Whittaker–Schwartz estimate -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance schwartzGaugeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance schwartzGaugeSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance schwartzGaugeIdeleMeasurable (F : Type u) [Field F] [NumberField F] :
    MeasurableSpace (Ideles F) := borel _
local instance schwartzGaugeIdeleBorel (F : Type u) [Field F] [NumberField F] :
    BorelSpace (Ideles F) := ⟨rfl⟩
local instance schwartzGaugeIdeleLocallyCompact
    (F : Type u) [Field F] [NumberField F] : LocallyCompactSpace (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance schwartzGaugeIdeleSecondCountable
    (F : Type u) [Field F] [NumberField F] : SecondCountableTopology (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

/-- The unchanged weighted Whittaker–Schwartz estimate, uniformly over
standard characters, vectors and Schwartz–Bruhat functions. -/
theorem whittakerSchwartzGauge : WhittakerSchwartzGaugeStatement.{u} := by
  apply whittakerSchwartzGauge_of_majorization_torusMajorants
    whittakerSimpleRootMajorization
  intro F _ _ _ r τ hτ
  refine ⟨τ + 3 + ∑ j : Fin (r + 1),
    ((((j : ℕ) + 1) * (r - (j : ℕ)) : ℕ) : ℝ), by positivity,
    Measure.haar, inferInstance, ?_⟩
  intro σ hσ φ hφ ψ hψ
  exact lintegral_gaugeSchwartzTorusMajorant_lt_top_of_large
    F r Measure.haar hφ hψ hτ hσ

end Langlands.Global.RankinSelbergGlobal
