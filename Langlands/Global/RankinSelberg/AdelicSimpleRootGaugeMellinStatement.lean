import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge

/-! # Padded Mellin integrability of adelic simple-root gauges -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

private local instance gaugeStatementSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- A right half-plane of convergence for every simple-root gauge after
restriction to any proper upper-left general linear block. This statement
contains no Whittaker functions or automorphic realizations. -/
def AdelicSimpleRootGaugeMellinStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r) (τ : ℝ), 0 ≤ τ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ Ξ : Points F (r + 1) → ℝ≥0∞,
        IsAdelicSimpleRootGauge F r τ Ξ → ∀ σ : ℝ, C < σ →
          ∫⁻ p : WhittakerQuotient F (t + 1),
              Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) p.out) *
                ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
            ∂whittakerQuotientMeasure F (t + 1) < ⊤


end Langlands.Global.RankinSelbergGlobal
