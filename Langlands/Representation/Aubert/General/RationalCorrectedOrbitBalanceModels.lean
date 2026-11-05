import Langlands.Representation.Aubert.General.RationalCorrectedOrbitHaarAdapter
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Actual group-scheme models for the corrected-orbit Haar balance -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

namespace CorrectedOrbitCocharacterRealization

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
    {I K : Finset (SimpleRoot i ν)} {m : rationalPoints G}
    (r : CorrectedOrbitCocharacterRealization i ν I K m)

local instance correctedOrbitBalanceModelsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- The original torus factors through the represented common centralizer. -/
def torusHom : T.toGrp ⟶ r.actingScheme :=
  Dynamic.torusFactor i (CommGroupScheme.groupHom r.zeta)
    (Dynamic.Affine.isRepresentedBy_centralizerHom
      (CommGroupScheme.groupHom r.zeta ≫ i))

@[reassoc (attr := simp)] theorem torusHom_comp : r.torusHom ≫ r.actingHom = i :=
  Dynamic.torusFactor_comp i (CommGroupScheme.groupHom r.zeta)
    (Dynamic.Affine.isRepresentedBy_centralizerHom
      (CommGroupScheme.groupHom r.zeta ≫ i))

abbrev leftRadicalScheme :=
  Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom r.zeta ≫ i)

abbrev rightRadicalScheme :=
  Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom r.eta ≫ i)

def leftRadicalHom : r.leftRadicalScheme ⟶ G :=
  Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom r.zeta ≫ i)

def rightRadicalHom : r.rightRadicalScheme ⟶ G :=
  Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom r.eta ≫ i)

theorem leftRadical_represented :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).IsRepresentedBy
      r.leftRadicalHom :=
  Dynamic.Affine.isRepresentedBy_unipotentHom _

theorem rightRadical_represented :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).IsRepresentedBy
      r.rightRadicalHom :=
  Dynamic.Affine.isRepresentedBy_unipotentHom _

theorem leftRadical_closed : IsClosedSubgroup r.leftRadicalHom :=
  Dynamic.Affine.isClosedSubgroup_unipotentHom _

theorem rightRadical_closed : IsClosedSubgroup r.rightRadicalHom :=
  Dynamic.Affine.isClosedSubgroup_unipotentHom _

/-- The scheme-theoretic intersection of the two actual positive radicals. -/
def intersectionScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  subgroupIntersection r.leftRadicalHom r.rightRadicalHom

/-- Its inclusion into the original ambient group. -/
def intersectionHom : r.intersectionScheme ⟶ G :=
  subgroupIntersectionHom r.leftRadicalHom r.rightRadicalHom

theorem intersection_closed : IsClosedSubgroup r.intersectionHom :=
  isClosedSubgroup_subgroupIntersectionHom r.leftRadical_closed r.rightRadical_closed

theorem intersection_represented :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).IsRepresentedBy
        r.intersectionHom := by
  have h := isRepresentedBy_subgroupIntersectionHom r.leftRadical_closed r.rightRadical_closed
  rw [r.leftRadical_represented.2, r.rightRadical_represented.2] at h
  exact h

/-- Actual points of the closed intersection scheme are precisely the literal
corrected-orbit intersection in the original rational point group. -/
def intersectionPointEquiv : rationalPoints r.intersectionScheme ≃*
    CorrectedFiltration.orbitUnipotentIntersection (unipotent i ν I) (unipotent i ν K) m :=
  (r.intersection_represented.pointsEquiv (Over.mk (𝟙 _))).trans
    (MulEquiv.subgroupCongr r.intersection_points)

@[simp] theorem intersectionPointEquiv_coe (z : rationalPoints r.intersectionScheme) :
    (r.intersectionPointEquiv z : rationalPoints G) =
      rationalPoints.map r.intersectionHom z := rfl

instance leftRadical_isAffineHom : IsAffineHom r.leftRadicalScheme.X.hom :=
  r.leftRadical_closed.isAffineHom

instance rightRadical_isAffineHom : IsAffineHom r.rightRadicalScheme.X.hom :=
  r.rightRadical_closed.isAffineHom

instance intersection_isAffineHom : IsAffineHom r.intersectionScheme.X.hom :=
  r.intersection_closed.isAffineHom

variable [LocallyOfFiniteType G.X.hom]

instance leftRadical_locallyOfFiniteType : LocallyOfFiniteType r.leftRadicalScheme.X.hom :=
  r.leftRadical_closed.locallyOfFiniteType

instance rightRadical_locallyOfFiniteType : LocallyOfFiniteType r.rightRadicalScheme.X.hom :=
  r.rightRadical_closed.locallyOfFiniteType

instance intersection_locallyOfFiniteType : LocallyOfFiniteType r.intersectionScheme.X.hom :=
  r.intersection_closed.locallyOfFiniteType

/-- Canonical natural finite coordinates of the first full radical's actual Lie kernel. -/
def leftRadicalCoordinates : Lie.FiniteCoordinates r.leftRadicalScheme
    (Module.finrank k (Additive (lieKernel r.leftRadicalScheme k))) :=
  Lie.finiteCoordinates r.leftRadicalScheme

/-- Canonical natural finite coordinates of the second full radical's actual Lie kernel. -/
def rightRadicalCoordinates : Lie.FiniteCoordinates r.rightRadicalScheme
    (Module.finrank k (Additive (lieKernel r.rightRadicalScheme k))) :=
  Lie.finiteCoordinates r.rightRadicalScheme

/-- Canonical natural finite coordinates of the literal intersection's actual Lie kernel. -/
def intersectionCoordinates : Lie.FiniteCoordinates r.intersectionScheme
    (Module.finrank k (Additive (lieKernel r.intersectionScheme k))) :=
  Lie.finiteCoordinates r.intersectionScheme

end CorrectedOrbitCocharacterRealization

end Langlands.Aubert.General.RationalPointFamily
