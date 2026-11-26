import Langlands.BruhatTits.Iwasawa.PointProducts
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Iwasawa decomposition at the inherited integral subgroup of each standard Levi -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.SpecialCompact

/-- Each actual standard Levi has both Iwasawa products with its own minimal
standard parabolic, using the preimage of the ambient standard integral points. -/
def GeneralLinearIntegralLeviIwasawaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N)))),
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
    IsGenericCocharacter i ν →
      ∀ J ⊆ simpleRelativeRoots i ν,
        haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
          (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
        let KJ := K.comap (rationalPoints.map (Standard.leviHom i ν J))
        let iJ := Standard.leviTorusHom i ν J
        IsCompactOpenMaximal F KJ ∧
          Iwasawa.PointProductEqualities (standardParabolicPoints iJ ν ∅) KJ

end Langlands.BruhatTits.SpecialCompact
