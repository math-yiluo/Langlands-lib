import Langlands.GroupScheme.Rational.SteinbergTopCoefficient
import Langlands.GroupScheme.Rational.SimpleRootHighestCoefficientNonvanishing

/-! # Actual unit diagonal and unconditional Steinberg character triangularity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The arbitrary-field local theorem supplies the published algebraically
closed local nonvanishing statement. -/
private theorem simpleRootHighestCoefficientNonvanishingForTriangularity :
    SplitSimpleRootHighestCoefficientNonvanishingStatement.{u} := by
  intro k _ _ G _ p d rho lam h a hpair x s v hv hv0
  exact x.coefficientMatrix_one_reflected_ne_zero rho h hpair s hv hv0

namespace SplitPinning

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)

/-- The actual own-variable coefficient of a fundamental trace is nonzero. -/
theorem fundamentalTraceDiagonal_ne_zero (i : Fin r) :
    fundamentalTraceDiagonal e x s F i ≠ 0 :=
  fundamentalTraceDiagonal_ne_zero_of_simpleRootHighestCoefficient e x s F
    simpleRootHighestCoefficientNonvanishingForTriangularity i

/-- The actual own-variable trace coefficient, regarded as a unit. -/
def fundamentalTraceDiagonalUnit (i : Fin r) : kˣ :=
  Units.mk0 (fundamentalTraceDiagonal e x s F i)
    (fundamentalTraceDiagonal_ne_zero e x s F i)

@[simp] theorem fundamentalTraceDiagonalUnit_val (i : Fin r) :
    (fundamentalTraceDiagonalUnit e x s F i : k) =
      fundamentalTraceDiagonal e x s F i := rfl

/-- The supplied trace coordinates have the canonical unit diagonal and the
already constructed lower remainders. -/
theorem steinbergRestriction_fundamentalCharacter (i : Fin r) :
    steinbergRestriction e x s (F (e i)).character =
      MvPolynomial.C (fundamentalTraceDiagonalUnit e x s F i : k) *
        MvPolynomial.X i + fundamentalTraceRemainder e x s F i := by
  rw [fundamentalTraceDiagonalUnit_val, fundamentalTraceRemainder]
  ring

/-- Actual fundamental trace characters are triangular on every supplied
Steinberg product over an algebraically closed field. -/
theorem hasTriangularFundamentalRestriction :
    HasTriangularFundamentalRestriction e x s F :=
  hasTriangularFundamentalRestriction_of_diagonal_ne_zero e x s F
    (fundamentalTraceDiagonal_ne_zero e x s F)

end SplitPinning

/-- Unconditional proof of the published triangular-character proposition. -/
theorem splitSteinbergCharacterTriangular :
    SplitSteinbergCharacterTriangularStatement.{u} :=
  splitSteinbergCharacterTriangular_of_simpleRootHighestCoefficient
    simpleRootHighestCoefficientNonvanishingForTriangularity

end Langlands.GroupScheme
