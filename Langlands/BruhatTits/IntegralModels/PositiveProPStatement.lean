import Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen
import Langlands.Cohomology.DivisibleSystem.ProPInvariants

/-! # Pro-`p` radical preimages in smooth local integral models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.IntegralModels

/-- The radical preimage of a supplied smooth connected-fibre neutral model
is pro-`p` in the point topology over a nonarchimedean local field. -/
def LocalFieldPositiveProPStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (D : RelativeComponentModelData 𝒪[F] F G)
    (Q : SpecialFibreQuotientData D),
    Q.IsReductiveQuotient →
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      Langlands.Cohomology.IsProPSubgroup (ringChar 𝓀[F]) Q.positivePoints

end Langlands.BruhatTits.IntegralModels
