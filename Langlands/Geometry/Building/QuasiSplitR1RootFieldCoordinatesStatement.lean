import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.GaloisPointRational

/-! # Actual field coordinates and the full centralizer action for type R1 roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}

/-- Finite separable field coordinates on the actual rational root subgroup,
with an actual character describing the action of the whole centralizer. -/
structure RootFieldCoordinates (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (s : S.toGrp ⟶ Z) (a : characterLattice S) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra k extension]
  [finite : FiniteDimensional k extension]
  [separable : Algebra.IsSeparable k extension]
  equiv : Multiplicative extension ≃* rootGroupPoints i a
  character : rationalCharacters (GaloisPointComparison.baseChanged k extension Z)
  restriction :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k extension)).map s)
        character =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k extension)
        ((rationalCharacters.equivCharacterLattice S).symm a)
  conjugation : ∀ (z : rationalPoints Z) (x : extension),
    rationalPoints.map j z * (equiv (Multiplicative.ofAdd x) : rationalPoints G) *
        (rationalPoints.map j z)⁻¹ =
      (equiv (Multiplicative.ofAdd
        ((rationalCharacterEval character
          (GaloisPointComparison.rationalExtend k extension Z z) : extension) * x)) :
            rationalPoints G)

attribute [instance] RootFieldCoordinates.field RootFieldCoordinates.algebra
  RootFieldCoordinates.finite RootFieldCoordinates.separable

/-- Every type R1 root of a quasi-split group has actual finite separable
field coordinates, with its entire centralizer acting through an actual
extension-field character restricting to the root. No coordinates or
valuation data are supplied as hypotheses. -/
def QuasiSplitR1RootFieldCoordinatesStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsQuasiSplit G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (Z : GroupScheme (Spec (CommRingCat.of k))) (j : Z ⟶ G),
        (torusCentralizer i).IsRepresentedBy j →
        ∀ (s : S.toGrp ⟶ Z), s ≫ j = i →
        ∀ a : characterLattice S,
          a ∈ RelativeRoot.indivisibleRoots i → 2 • a ∉ relativeRoots i →
            Nonempty (RootFieldCoordinates i j s a)

end Langlands.Geometry.Building
