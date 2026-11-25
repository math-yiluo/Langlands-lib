import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.Interface

/-! # Global pointwise Whittaker majorization by simple-root gauges -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

private local instance gaugeStatementSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- A pointwise adelic gauge estimate for an analytic decay space with one
central power exponent. The gauge exponent is uniform over its vectors and
over standard additive characters. -/
def WhittakerSimpleRootMajorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (V : Submodule ℂ (Points F (r + 1) → ℂ))
    (R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V),
    WhittakerDecayClass F r V R → ∀ β : ℝ,
      (∀ f : V, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
        ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β) →
      ∃ τ : ℝ, 0 ≤ τ ∧ ∀ (ψ : AddChar (Adeles F) ℂ),
        IsStandardAdditiveCharacter F ψ → ∀ f : V,
          ∃ Ξ : Points F (r + 1) → ℝ≥0∞, IsAdelicSimpleRootGauge F r τ Ξ ∧
            ∀ g : Points F (r + 1),
              ‖whittaker F r ψ f g‖ₑ ≤
                ENNReal.ofReal (detNorm F (r + 1) g ^ β) * Ξ g

end Langlands.Global.RankinSelbergGlobal
