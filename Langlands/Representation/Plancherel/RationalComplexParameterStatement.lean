import Langlands.Representation.Plancherel.RationalImageComplexExponential

/-! # Periods and lifts of actual unramified complex characters -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- The algebraic exponential, period, lift and imaginary-image assertions of
Renard V.3.20 on the actual general-group rational valuation image, together
with surjectivity and equality of lifts on canonical rational points. -/
def RationalComplexParameterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    Function.Surjective (rationalImageComplexCharacter G) ∧
      (∀ lam : rationalImageComplexFunctionals G,
        rationalImageComplexCharacter G lam = 1 ↔ lam ∈ rationalImagePeriodLattice G) ∧
      (∀ lam mu : rationalImageComplexFunctionals G,
        rationalImageComplexCharacter G lam = rationalImageComplexCharacter G mu ↔
          lam - mu ∈ rationalImagePeriodLattice G) ∧
      (∀ (chi : rationalImageCharacters G) (lam : rationalImageComplexFunctionals G),
        rationalImageComplexCharacter G lam = chi →
          rationalImageParameterRealPart G lam = rationalImageRealPart G chi) ∧
      (∀ lam : rationalImageComplexFunctionals G,
        rationalImageComplexCharacter G lam ∈
            unitaryCharacters (rationalDiscreteValuationImage G) ↔
          rationalImageParameterRealPart G lam = 0) ∧
      (∀ chi : rationalImageCharacters G,
        chi ∈ unitaryCharacters (rationalDiscreteValuationImage G) ↔
          ∃ phi : rationalImageRealFunctionals G,
            rationalImageComplexCharacter G (Complex.I • rationalImageParameterOfReal G phi) =
              chi) ∧
      Function.Surjective (rationalCanonicalUnramifiedComplexExponential G) ∧
      (∀ lam mu : rationalImageComplexFunctionals G,
        rationalCanonicalUnramifiedComplexExponential G (Multiplicative.ofAdd lam) =
            rationalCanonicalUnramifiedComplexExponential G (Multiplicative.ofAdd mu) ↔
          lam - mu ∈ rationalImagePeriodLattice G)

end Langlands.Plancherel
