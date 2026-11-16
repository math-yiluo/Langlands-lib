import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Reductive.BasedBorelPullback

/-! # Affine pinned models and their comparisons on arbitrary schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- An affine split reductive group with its full coordinate root datum,
chosen base, and trivialized simple-root Lie spaces. This is supplied data. -/
structure AffinePinnedModel where
  ring : Type u
  [commRing : CommRing ring]
  group : GroupScheme (Spec (CommRingCat.of ring))
  reductive : IsReductive group
  coordinates : Type u
  [fintypeCoordinates : Fintype coordinates]
  inclusion : splitTorus (Spec (CommRingCat.of ring)) coordinates ⟶ group
  closed : IsClosedSubgroup inclusion
  maximal : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of ring)) coordinates) inclusion
  rootIndex : Type u
  [fintypeRoots : Fintype rootIndex]
  rootDatum : RootDatum rootIndex (coordinates → ℤ) (coordinates → ℤ)
  fibrewiseRootDatum : letI := reductive.isAffineHom
    IsFibrewiseRootDatumOf coordinates group inclusion rootDatum
  rootLines : letI := reductive.isAffineHom
    ∀ a : rootIndex, Nonempty
      (splitTorus.exponentWeightSpace coordinates group inclusion (rootDatum.root a)
        ≃ₗ[CommRingCat.of ring] CommRingCat.of ring)
  basis : rootDatum.Base
  pinning : letI := reductive.isAffineHom
    ∀ a : basis.support, CommRingCat.of ring ≃ₗ[CommRingCat.of ring]
      splitTorus.exponentWeightSpace coordinates group inclusion (rootDatum.root a)

attribute [instance] AffinePinnedModel.commRing AffinePinnedModel.fintypeCoordinates
  AffinePinnedModel.fintypeRoots

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- The original affine base of a supplied model. -/
abbrev base : Scheme.{u} := Spec (CommRingCat.of M.ring)

instance : IsAffineHom M.group.X.hom := M.reductive.isAffineHom

/-- The actual pullback group of a model along an arbitrary scheme morphism. -/
abbrev groupOver {T : Scheme.{u}} (f : T ⟶ M.base) : GroupScheme T :=
  (GroupScheme.baseChange f).obj M.group

/-- The normalized coordinate split torus inclusion on that arbitrary scheme. -/
def inclusionOver {T : Scheme.{u}} (f : T ⟶ M.base) :
    splitTorus T M.coordinates ⟶ M.groupOver f :=
  BasedBorelTransport.baseChangeInclusion f M.inclusion

/-- The actual canonical positive-coroot cocharacter on that arbitrary scheme. -/
def cocharacterOver {T : Scheme.{u}} (f : T ⟶ M.base) :
    (Gm T).toGrp ⟶ M.groupOver f :=
  BasedBorelTransport.cocharacter (M.inclusionOver f) M.rootDatum M.basis

variable {M} {N K : AffinePinnedModel.{u}} {T W : Scheme.{u}}

/-- Actual isomorphisms between two models pulled back to a common test scheme.
The original affine bases, coordinate ranks and root types may differ. -/
abbrev Comparison (f : T ⟶ M.base) (g : T ⟶ N.base) :=
  M.groupOver f ≅ N.groupOver g

/-- Pull a comparison back and express its endpoints as direct pullbacks. -/
def pullComparison {f : T ⟶ M.base} {g : T ⟶ N.base}
    (e : Comparison f g) (q : W ⟶ T) : Comparison (q ≫ f) (q ≫ g) :=
  baseChangeCompIso f q M.group ≪≫ (GroupScheme.baseChange q).mapIso e ≪≫
    (baseChangeCompIso g q N.group).symm

@[simp] theorem pullComparison_refl (f : T ⟶ M.base) (q : W ⟶ T) :
    pullComparison (Iso.refl (M.groupOver f)) q = Iso.refl _ := by
  apply Iso.ext
  simp [pullComparison]

@[simp] theorem pullComparison_trans {f : T ⟶ M.base} {g : T ⟶ N.base}
    {h : T ⟶ K.base} (e : Comparison f g) (d : Comparison g h) (q : W ⟶ T) :
    pullComparison (e ≪≫ d) q = pullComparison e q ≪≫ pullComparison d q := by
  apply Iso.ext
  simp [pullComparison]

@[simp] theorem pullComparison_symm {f : T ⟶ M.base} {g : T ⟶ N.base}
    (e : Comparison f g) (q : W ⟶ T) :
    pullComparison e.symm q = (pullComparison e q).symm := by
  apply Iso.ext
  simp [pullComparison]

end AffinePinnedModel

end Langlands.GroupScheme
