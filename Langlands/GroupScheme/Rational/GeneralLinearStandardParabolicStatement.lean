import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.GeneralLinearIndexing

/-! # Standard parabolics of the general linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Adjacent simple roots, block standard subgroups and their actual rational points
for the diagonal torus of `GL_N`, with a strictly decreasing generic cocharacter. -/
def GeneralLinearStandardParabolicStatement : Prop :=
  ∀ (k : Type u) [Field k] (N : ℕ),
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of k)
    let pointMap :=
      (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom).comp
        (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k)
          (Over.mk (𝟙 (Spec (CommRingCat.of k))))).toMonoidHom
    ∀ ν : cocharacterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N))),
      IsGenericCocharacter i ν →
      StrictAnti (GeneralLinear.cocharacterCoordEquiv (Fin N) k ν) →
        simpleRelativeRoots i ν = Set.range (GeneralLinear.simpleRootCharacter k) ∧
        (∀ B : Langlands.GeneralLinear.BlockShape N,
          let J := GeneralLinear.blockSimpleRoots k B
          standardParabolic i ν J =
              GeneralLinear.blockShapeParabolic B (CommRingCat.of k) ∧
          standardLevi i ν J =
              GeneralLinear.blockShapeLevi B (CommRingCat.of k) ∧
          standardUnipotent i ν J =
              GeneralLinear.blockShapeUnipotent B (CommRingCat.of k) ∧
          standardParabolicPoints i ν J = (B.parabolic k).comap pointMap ∧
          standardLeviPoints i ν J = (B.leviSubgroup k).comap pointMap ∧
          standardUnipotentPoints i ν J = (B.unipotentSubgroup k).comap pointMap) ∧
        ∀ J : Set (characterLattice
            (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N)))),
          J ⊆ simpleRelativeRoots i ν →
            ∃! B : Langlands.GeneralLinear.BlockShape N,
              GeneralLinear.blockSimpleRoots k B = J

end Langlands.GroupScheme
