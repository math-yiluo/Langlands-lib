import Langlands.GroupScheme.Reductive.AffinePinnedComparisonProperties
import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Canonical Borel subgroups of actual affine pinned models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u})

local instance : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- The actual canonical Borel over the original coefficient ring. -/
abbrev borel : GroupScheme M.base :=
  AffineRegularBorel.borel M.inclusion
    (BasedBorelExponent.positiveCorootSum M.rootDatum M.basis)

/-- The actual canonical Borel inclusion. -/
abbrev borelInclusion : M.borel ⟶ M.group :=
  AffineRegularBorel.inclusion M.inclusion
    (BasedBorelExponent.positiveCorootSum M.rootDatum M.basis)

/-- The canonical based dynamic parabolic is a relative Borel. -/
theorem isRelativeBorel_borelInclusion :
    IsRelativeBorelSubgroup M.borelInclusion :=
  AffineRegularBorel.isRelativeBorel_positiveCorootSum M.inclusion M.rootDatum
    M.basis M.fibrewiseRootDatum M.reductive M.maximal

/-- The Borel inclusion is closed. -/
theorem isClosedSubgroup_borelInclusion : IsClosedSubgroup M.borelInclusion :=
  Dynamic.Affine.isClosedSubgroup_parabolicHom _

/-- Factor the original coordinate torus through the canonical Borel. -/
def torusToBorel : splitTorus M.base M.coordinates ⟶ M.borel :=
  (Dynamic.Affine.isRepresentedBy_parabolicHom _).factorHom M.inclusion
    (by
      rw [← (Dynamic.Affine.isRepresentedBy_parabolicHom _).2]
      exact AffineRegularBorel.torus_range_le M.inclusion
        (BasedBorelExponent.positiveCorootSum M.rootDatum M.basis))

theorem torusToBorel_comp : M.torusToBorel ≫ M.borelInclusion = M.inclusion :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The actual pullback of the original canonical Borel. -/
abbrev borelOver {T : Scheme.{u}} (f : T ⟶ M.base) : GroupScheme T :=
  (baseChange f).obj M.borel

/-- Its actual inclusion into the pulled-back ambient group. -/
abbrev borelInclusionOver {T : Scheme.{u}} (f : T ⟶ M.base) :
    M.borelOver f ⟶ M.groupOver f :=
  (baseChange f).map M.borelInclusion

/-- The actual coordinate torus map into the pulled-back Borel. -/
def torusToBorelOver {T : Scheme.{u}} (f : T ⟶ M.base) :
    splitTorus T M.coordinates ⟶ M.borelOver f :=
  (splitTorus.baseChangeIso f M.coordinates).inv ≫ (baseChange f).map M.torusToBorel

theorem torusToBorelOver_comp {T : Scheme.{u}} (f : T ⟶ M.base) :
    M.torusToBorelOver f ≫ M.borelInclusionOver f = M.inclusionOver f := by
  simp only [torusToBorelOver, borelInclusionOver, Category.assoc,
    ← Functor.map_comp, torusToBorel_comp]
  rfl

/-- The pulled-back canonical Borel is relative Borel over any common scheme. -/
theorem isRelativeBorel_borelInclusionOver {T : Scheme.{u}} (f : T ⟶ M.base) :
    IsRelativeBorelSubgroup (M.borelInclusionOver f) :=
  M.isRelativeBorel_borelInclusion.baseChange M.reductive f

/-- Its inclusion remains closed under arbitrary pullback. -/
theorem isClosedSubgroup_borelInclusionOver {T : Scheme.{u}} (f : T ⟶ M.base) :
    IsClosedSubgroup (M.borelInclusionOver f) :=
  M.isClosedSubgroup_borelInclusion.baseChange f

/-- Ambient maximality reflects to the actual canonical Borel on each fibre. -/
theorem isFibrewiseMaximalTorus_torusToBorelOver {T : Scheme.{u}}
    (f : T ⟶ M.base) :
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme T M.coordinates)
      (M.torusToBorelOver f) := by
  let : Smooth M.group.X.hom := M.reductive.smooth
  have hmax := splitTorus.isFibrewiseMaximalTorus_baseChangedHom
    M.coordinates M.group M.inclusion M.maximal f
  intro s
  apply IsMaximalTorus.of_comp
    ((M.isClosedSubgroup_borelInclusionOver f).baseChange (T.fromSpecResidueField s))
  rw [← Functor.map_comp, torusToBorelOver_comp]
  exact hmax s

/-- Direct and iterated Borel inclusions are related by the actual
base-change comparison at each endpoint. -/
theorem borelInclusionOver_pull {T W : Scheme.{u}} (f : T ⟶ M.base) (q : W ⟶ T) :
    (baseChangeCompIso f q M.borel).hom ≫
        (baseChange q).map (M.borelInclusionOver f) ≫
        (baseChangeCompIso f q M.group).inv = M.borelInclusionOver (q ≫ f) := by
  have h := ((Functor.mapGrpNatIso (Over.pullbackComp q f)) ≪≫
    Functor.mapGrpCompIso).hom.naturality M.borelInclusion
  change M.borelInclusionOver (q ≫ f) ≫ (baseChangeCompIso f q M.group).hom =
    (baseChangeCompIso f q M.borel).hom ≫
      (baseChange q).map (M.borelInclusionOver f) at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme.AffinePinnedModel
