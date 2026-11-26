import Langlands.BruhatTits.Iwasawa.PointProducts
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Iwasawa decomposition at the standard integral subgroup of `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

/-- The standard integral subgroup is maximal compact and open, and it gives both
Iwasawa products for each minimal standard parabolic of the diagonal torus. -/
def GeneralLinearIntegralIwasawaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N)))),
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
    IsGenericCocharacter i ν →
      IsCompactOpenMaximal F K ∧
        Iwasawa.PointProductEqualities (standardParabolicPoints i ν ∅) K

end Langlands.BruhatTits.SpecialCompact
