import Langlands.Representation.CuspidalSupport.RationalInertiaCoproducts
import Langlands.Representation.CuspidalSupport.RationalInertiaPresentations
import Langlands.Representation.Category.CoproductCompression
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual smooth coproducts of rational inertia-block objects

The actual block inclusion preserves the concrete direct-sum colimits.
Consequently every coproduct in the block has its expected actual smooth
direct-sum carrier.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uI

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable (π : SmoothRep.{0, uF, max uI uV} ℂ (GroupScheme.rationalPoints G))
  {I : Type uI}

/-- The actual block inclusion preserves each coproduct whose index universe
fits in the carrier universe. -/
instance rationalInertiaBlockInclusion_preservesCoproduct
    (A : I → RationalInertiaBlock G π) :
    PreservesColimit (Discrete.functor A) (rationalInertiaBlockProperty G π).ι := by
  classical
  apply preservesColimit_of_preserves_colimit_cocone
    (rationalInertiaBlockDirectSumIsColimit G π A)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  exact SmoothRep.directSumIsColimit (fun i => (A i).obj)

/-- The inclusion preserves every diagram over the given discrete index type. -/
instance rationalInertiaBlockInclusion_preservesColimitsOfShape :
    PreservesColimitsOfShape (Discrete I) (rationalInertiaBlockProperty G π).ι :=
  preservesColimitsOfShape_of_discrete _

/-- The smooth cofan obtained from any block coproduct is a coproduct. -/
def rationalInertiaBlockSmoothCofanIsColimit
    (A : I → RationalInertiaBlock G π) (s : Cofan A) (hs : IsColimit s) :
    IsColimit (Cofan.mk s.pt.obj (fun i => (s.inj i).hom) :
      Cofan (fun i => (A i).obj)) := by
  exact isColimitCofanMkObjOfIsColimit
    (rationalInertiaBlockProperty G π).ι A (fun i => s.inj i) hs

/-- The actual summation map identifies the carrier of any block coproduct
with the algebraic direct sum of its actual summands. -/
def rationalInertiaBlockCofanDirectSumEquiv [DecidableEq I]
    (A : I → RationalInertiaBlock G π) (s : Cofan A) (hs : IsColimit s) :
    (Representation.directSum (fun i => (A i).obj.representation)).Equiv
      s.pt.obj.representation :=
  SmoothRep.cofanDirectSumEquiv (fun i => (A i).obj)
    (Cofan.mk s.pt.obj (fun i => (s.inj i).hom))
    (rationalInertiaBlockSmoothCofanIsColimit G π A s hs)

end Langlands.CuspidalSupport
