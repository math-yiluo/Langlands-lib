import Langlands.Representation.RankinSelberg.RationalZeta
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Algebraic normalization of rational gamma equations

The two incidence hypotheses and the normalized Laurent-module generators
determine one nonzero monomial for every pair satisfying the gamma equation.
This module states the algebraic prerequisite; it does not prove it or assert
an analytic functional equation.
-/

namespace Langlands.RankinSelberg

/-- Normalize a rational gamma equation by two normalized JPSS generators.
The constants are uniform over all rational pairs satisfying the gamma equation,
and the conclusion retains the existing full reduced-denominator domain. -/
def GammaNormalizationStatement : Prop :=
  ∀ (q : ℕ), 1 < q →
    ∀ (ζ : ℂˣ) (e : ℕ) (G : RationalFunctions)
      (S T : Set RationalFunctions) (P Pdual : Polynomial ℂ),
      IsNormalizedGenerator S P →
      IsNormalizedGenerator T Pdual →
      (∀ R ∈ S, ∃ Rdual ∈ T, GammaFunctionalEquation q ζ e G R Rdual) →
      (∀ Rdual ∈ T, ∃ R ∈ S, GammaFunctionalEquation q ζ e G R Rdual) →
      ∃ (c : ℂˣ) (m : ℤ), ∀ (R Rdual : RationalFunctions),
        GammaFunctionalEquation q ζ e G R Rdual →
        NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual

end Langlands.RankinSelberg
