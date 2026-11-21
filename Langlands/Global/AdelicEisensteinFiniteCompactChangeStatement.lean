import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicParabolicQuotient

/-! # Finite changes of the adelic Iwasawa compact -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- When two maximal Iwasawa compacts have the same infinite projection,
the parameter twist for the first is a finite sum of twists for the second
with fixed automorphic inducing functions and exponential coefficients. -/
def EisensteinFiniteCompactChangeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (K K₂ : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact p K) (hK₂ : IsIwasawaCompact p K₂),
    IsMaximalCompactSubgroup F G K → IsMaximalCompactSubgroup F G K₂ →
    K.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (φ : AdelicGroupPoints F G → ℂ),
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l) Kinf rho φ →
      ∃ (S : Finset (RealCharacterDual F P))
        (cut : RealCharacterDual F P → AdelicGroupPoints F G → ℂ),
        (∀ v ∈ S, IsAutomorphicFunctionOn F G hsmooth hcalc
          (parabolicQuotientSubgroup F p iU l) Kinf rho (cut v)) ∧
        ∀ (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G),
          hK.parameterTwist φ lam g =
            ∑ v ∈ S, Complex.exp (complexParameterPairing F P lam v) *
              hK₂.parameterTwist (cut v) lam g

end Langlands.Global
