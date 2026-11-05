import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.SimultaneousStandardConjugation

/-! # Fixed-family standardization of specified parabolic and Levi maps

The dynamic parabolic and radical statements, maximal split torus conjugacy
and actual relative roots remain explicit structural inputs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Choose one rational point standardizing the two specified subgroup images
in the fixed family, using only the explicit dynamic and conjugacy inputs. -/
def parabolicLeviStandardConjugatingPoint
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T}
    (hroot : letI := hG.isAffineHom
      letI := hi.isSplitSubtorus.mono
      HasRelativeRootSystem i)
    (hν : letI := hG.isAffineHom; IsGenericCocharacter i ν)
    (p : P ⟶ G) (l : M ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    letI := hG.isAffineHom
    {g : rationalPoints G //
      ∃ (J : Set (characterLattice T)) (ζ : cocharacterLattice T),
        IsStandardCocharacter i ν J ζ ∧
        SubgroupFunctor.range (p ≫ (G.innerIso g).hom) = standardParabolic i ν J ∧
        SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) = standardLevi i ν J ∧
        SubgroupFunctor.range (p ≫ (G.innerIso g).hom) =
          Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) ∧
        SubgroupFunctor.range (l ≫ p ≫ (G.innerIso g).hom) =
          Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)} := by
  have := hG.isAffineHom
  let z := DynamicLeviConjugacy.parabolicLeviRealizingCocharacter hPD hGUR hG hp hl
  have hspec :=
    DynamicLeviConjugacy.parabolicLeviRealizingCocharacter_spec hPD hGUR hG hp hl
  exact simultaneousStandardConjugatingPoint
    hconj hG hi hroot hν p l z hspec.1 hspec.2

end Langlands.GroupScheme
