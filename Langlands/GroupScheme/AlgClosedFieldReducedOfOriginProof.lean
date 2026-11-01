import Langlands.GroupScheme.AlgClosedFieldReducedOfOriginStatement
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u

private lemma reduced_affine_of_closed_stalks
    {X : Scheme.{u}} [JacobsonSpace X] (R : CommRingCat.{u})
    (f : Spec R ⟶ X) [IsOpenImmersion f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → _root_.IsReduced (X.presheaf.stalk x)) :
    AlgebraicGeometry.IsReduced (Spec R) := by
  apply (affine_isReduced_iff R).2
  apply isReduced_ofLocalizationMaximal R
  intro m hm
  let x : Spec R := ⟨m, hm.isPrime⟩
  have hxc : x ∈ closedPoints (Spec R) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).2 hm
  have hyc : IsClosed ({f x} : Set X) := by
    rw [← f.isOpenEmbedding.preimage_closedPoints] at hxc
    exact hxc
  have := h (f x) hyc
  have : _root_.IsReduced ((Spec R).presheaf.stalk x) :=
    isReduced_of_injective (asIso (f.stalkMap x)).inv.hom
      (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_injective (Spec.stalkIso R x).inv.hom
    (Spec.stalkIso R x).symm.commRingCatIsoToRingEquiv.injective

private lemma reduced_of_closed_stalks (X : Scheme.{u}) [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) → _root_.IsReduced (X.presheaf.stalk x)) :
    AlgebraicGeometry.IsReduced X := by
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover X X.affineCover).2
  intro i
  exact reduced_affine_of_closed_stalks _ (X.affineCover.f i) h

/-- Reducedness at the identity propagates over an algebraically closed field. -/
theorem algClosedFieldReducedOfOrigin : AlgClosedFieldReducedOfOriginStatement.{u} := by
  intro k _ _ P _ hft he
  have := hft
  let e : P.left := (η[P]).left (IsLocalRing.closedPoint k)
  have : _root_.IsReduced (P.left.presheaf.stalk e) := he
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace P.hom
  apply reduced_of_closed_stalks
  intro x hx
  let x' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P :=
    Over.homMk (pointOfClosedPoint P.hom x hx) (by simp)
  let α := GrpObj.mulRight x'
  have hα : η[P] ≫ α.hom = x' := by
    simpa [α, GrpObj.mulRight, comp_lift_assoc] using
      (CategoryTheory.MonObj.lift_comp_one_left (𝟙 _) x')
  have hα' : α.hom.left e = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint k))
    change α.hom.left e =
      pointOfClosedPoint P.hom x hx (IsLocalRing.closedPoint k) at h
    simpa only [pointOfClosedPoint_apply] using h
  rw [← hα']
  exact isReduced_of_injective (α.hom.left.stalkMap e).hom
    (asIso (α.hom.left.stalkMap e)).commRingCatIsoToRingEquiv.injective

end Langlands.GroupScheme
