import Langlands.Representation.Classification.Segments
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Derivative.Iteration

/-!
# Central exponents and positivity of shifted derivatives

Actual scalar characters and actual irreducible smooth subquotients express
Bernstein's central exponents. Positivity below a supplied order includes order
zero; no assertion that the supplied order is highest is built into the predicate.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- An actual scalar character has norm `|a|^e` on every scalar matrix.
For positive rank and an irreducible representation, this is Bernstein's
central exponent. The same formula also defines the rank-zero convention. -/
def HasBernsteinCentralExponent {n : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (e : ℝ) : Prop :=
  letI := T.topology
  ∃ ω : F.Carrierˣ →* ℂˣ,
    HasScalarCharacter A.representation GeneralLinear.scalar ω ∧
      ∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ = T.normalizedAbs (a : F.Carrier) ^ e

/-- Central exponents of actual irreducible smooth subquotients, in the
ambient carrier universe. This definition makes no existence assertion. -/
def bernsteinCentralExponents {n : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) : Set ℝ :=
  letI := T.topology
  {e | ∃ D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
    Representation.IsIrreducible D.representation ∧
      SmoothRep.IsSubquotient D A ∧ HasBernsteinCentralExponent T D e}

/-- Every central exponent of every irreducible subquotient is positive.
For the zero representation the condition is vacuous. -/
def BernsteinPositiveCentralExponents {n : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  ∀ e ∈ bernsteinCentralExponents T A, 0 < e

/-- The actual shifted derivative `ν^(1/2) A^(k)`, including the order-zero
case `ν^(1/2) A`. -/
abbrev bernsteinShiftedDerivative
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {n : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n - k) F.Carrier) :=
  T.segmentFactor ((Derivative.generalLinearDerivative T ψ n k hk).obj A) (1 / 2)

/-- All shifted derivatives of orders strictly below `h` have positive
central exponents, including order zero. The order `h` is supplied separately;
this predicate asserts neither nonvanishing at `h` nor vanishing above `h`. -/
def BernsteinShiftedDerivativePositiveBelow
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {n : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (h : ℕ) : Prop :=
  ∀ (k : ℕ) (hk : k ≤ n), k < h →
    BernsteinPositiveCentralExponents T (bernsteinShiftedDerivative T ψ A k hk)

end Langlands.Classification
