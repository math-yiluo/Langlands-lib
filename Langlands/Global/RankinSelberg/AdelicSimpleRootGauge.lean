import Langlands.Global.RankinSelberg.SchwartzBruhat
import Langlands.Global.AdelicGLStandardCompact
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices

/-! # Adelic gauges in simple-root coordinates -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance gaugeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The diagonal adelic point with the prescribed ideles on its diagonal. -/
def gaugeDiagonalPoint (n : ℕ) (d : Fin n → Ideles F) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d)

/-- The standard maximal compact subgroup, on the actual group-scheme points. -/
def gaugeStandardCompact (n : ℕ) : Subgroup (Points F n) :=
  (PrimitiveAdelicHeight.standardCompact F n).comap
    (GeneralLinearGroupPoints.adelicEquiv F n).toMonoidHom

/-- The adjacent diagonal ratios, as ideles. -/
def gaugeSimpleRootIdeles (r : ℕ) (d : Fin (r + 1) → Ideles F) :
    Fin r → Ideles F :=
  fun i => d i.castSucc / d i.succ

/-- The row of adjacent diagonal ratios, viewed in the additive adele space. -/
def gaugeSimpleRootRow (r : ℕ) (d : Fin (r + 1) → Ideles F) : RowVector F r :=
  fun _ i => (gaugeSimpleRootIdeles F r d i : Adeles F)

/-- The product of the normalized idelic absolute values of the simple roots. -/
def gaugeSimpleRootNormProduct (r : ℕ) (d : Fin (r + 1) → Ideles F) : ℝ :=
  ∏ i, ((IdeleAbsoluteValue.full F (gaugeSimpleRootIdeles F r d i) : ℝ≥0) : ℝ)

/-- A global simple-root gauge of exponent `τ`. Its torus restriction is
`|a₁ ⋯ aᵣ|⁻ᵗ ‖Φ(a₁, …, aᵣ)‖`, and it is left unipotent and right standard compact
invariant. The exponent is independent of the Schwartz–Bruhat function. -/
def IsAdelicSimpleRootGauge (r : ℕ) (τ : ℝ) (Ξ : Points F (r + 1) → ℝ≥0∞) : Prop :=
  0 ≤ τ ∧ Measurable Ξ ∧
    (∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      Ξ ((n : Points F (r + 1)) * g) = Ξ g) ∧
    (∀ (k : gaugeStandardCompact F (r + 1)) (g : Points F (r + 1)),
      Ξ (g * (k : Points F (r + 1))) = Ξ g) ∧
    ∃ Φ : RowVector F r → ℂ, Φ ∈ schwartzBruhat F r ∧
      ∀ d : Fin (r + 1) → Ideles F,
        Ξ (gaugeDiagonalPoint F (r + 1) d) =
          ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
            ‖Φ (gaugeSimpleRootRow F r d)‖ₑ

end Langlands.Global.RankinSelbergGlobal
