import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Reductive.RootDatum

/-! # The literal integral intersection in a standard Levi of `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.SpecialCompact

/-- The matrix images of the actual standard Levi and its intersection with the
standard integral subgroup are the block diagonal subgroup and its integral image. -/
def GeneralLinearStandardLeviIntegralPointsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] (N : ℕ),
    let T := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
      ∀ (J : Set (characterLattice T)) (ζ : cocharacterLattice T),
        IsStandardCocharacter i ν J ζ →
        let w := GeneralLinear.cocharacterCoordEquiv (Fin N) F ζ
        let L := standardLeviPoints i ν J
        let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
        let e := GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
        L.map e.toMonoidHom = GeneralLinear.blockLeviSubgroup F w ∧
          (K ⊓ L).map e.toMonoidHom =
            (GeneralLinear.blockLeviSubgroup 𝒪[F] w).map
              (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F))

end Langlands.BruhatTits.SpecialCompact
