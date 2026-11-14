import Langlands.GroupScheme.Rational.RootFieldVectorIso
import Langlands.Geometry.Building.RootFieldCoordinatesOfTorus

/-! # Scheme isomorphisms realizing the actual root-orbit field coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))

attribute [local instance] rootsGaloisAction

variable
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
    {q : U ⟶ G} (hq : (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ j) a).IsRepresentedBy q)
    {m : ℕ} (b : Module.Basis (Fin m) k (rootOrbitField k L j β))

/-- The actual root representative is isomorphic to the polynomial additive
space of the root-orbit field in any finite basis. -/
def rootFieldVectorIsoOfOrbit : U ≅ VectorGroup.groupScheme (CommRingCat.of k) m :=
  RelativeRoot.rootFieldVectorIso hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh hq
    (rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit) b

variable [IsAffine T.toGrp.X.left] [IsAffine S.toGrp.X.left]
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hβ : β ∈ rootRestrictionFiber k L j f a)

/-- The actual scheme isomorphism realizes exactly the published rational
root-field coordinates, rather than an unrelated additive parametrization. -/
theorem sectionCoordinates_rootFieldVectorIsoOfOrbit (g : rationalPoints U) :
    (VectorGroup.sectionCoordinates (CommRingCat.of k) m
      (rationalPoints.map
        (rootFieldVectorIsoOfOrbit k L f j hG hj hS hT ha hhigh β horbit hq b).hom g)).toAdd =
      b.equivFun
        (((rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT ha hhigh β hβ horbit).equiv.symm
          (hq.pointsEquiv _ g)).toAdd) := by
  rw [rootFieldVectorIsoOfOrbit, RelativeRoot.sectionCoordinates_rootFieldVectorIso]
  rfl

end Langlands.Geometry.Building
