import Langlands.Global.RankinSelberg.WhittakerExpansionCore.Interface
import Langlands.Global.RankinSelberg.EqualUnfoldingKernel

/-! # A weighted Whittaker–Schwartz estimate for analytic decay classes

This internal analytic statement isolates the global gauge integral needed by
the equal-rank unfolding, in a form that also applies to transpose-inverse
transports of cusp functions. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance whittakerSchwartzSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- One central exponent bounds every function of the space, with a separate
nonnegative multiplicative constant for each function. -/
def HasCentralPowerBound (r : ℕ) (V : Submodule ℂ (Points F (r + 1) → ℂ)) : Prop :=
  ∃ β : ℝ, ∀ f : V, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
    ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β

/-- A uniform right half-plane of finiteness for the Whittaker–Schwartz
integrals of a space of functions. The threshold is uniform over standard
characters, functions of the space, and Schwartz–Bruhat functions. -/
def WhittakerSchwartzBound [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (V : Submodule ℂ (Points F (r + 1) → ℂ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (f : V) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) → ∀ σ : ℝ, C < σ →
        ∫⁻ p : WhittakerQuotient F (r + 1),
            ‖whittaker F r ψ f p.out‖ₑ * ‖Φ (lastRow F r p.out)‖ₑ *
              ENNReal.ofReal (detNorm F (r + 1) p.out ^ σ)
          ∂whittakerQuotientMeasure F (r + 1) < ⊤

/-- The weighted Whittaker–Schwartz estimate for every analytic decay class
whose functions share a central-power exponent. -/
def WhittakerSchwartzGaugeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (V : Submodule ℂ (Points F (r + 1) → ℂ))
    (R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V),
    WhittakerDecayClass F r V R → HasCentralPowerBound F r V →
      WhittakerSchwartzBound F r V

end Langlands.Global.RankinSelbergGlobal
