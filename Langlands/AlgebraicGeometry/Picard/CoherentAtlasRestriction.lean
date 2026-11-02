import Langlands.AlgebraicGeometry.Picard.CoherentFamilyRankOnePointFactorization
import Langlands.AlgebraicGeometry.Picard.StackAtlasComparison
import Langlands.AlgebraicGeometry.Stacks.SchemeAtlasRestriction

/-! # Restricting a coherent-family atlas to actual line bundles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Picard

open CoherentSheaves Langlands.CategoryTheory.PseudofunctorPointFiberTransport
open Langlands.CategoryTheory.PseudofunctorHomLift

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [Flat f] [UniversallyClosed f] [LocallyOfFinitePresentation f]
  (α : Pseudofunctor.StrongTrans (PicardGroupoid.relativeHomLift f)
    (homLift.{u + 1} (FamilyGroupoid.pseudofunctor f)))
  (hα : ∀ T : Over S, (component α T).FullyFaithful)
  (hobj : ∀ (T : Over S) (η : (PicardGroupoid.relativeHomLift f).obj (.mk (op T))),
    (component α T).obj η =
      ULiftHom.objUp.{u + 1, u + 1}
        ((PicardGroupoid.relativeToFamily f T).obj (ULiftHom.objDown.{u + 1, u + 1} η)))
  {U : Over S} (M : FamilyGroupoid f U)

/-- The actual line bundle on the rank-one open maps to the restricted atlas
family, through the identity isomorphism of its underlying module. -/
def coherentRankOneAtlasImageIso :
    (component α (familyRankOneBase f M)).obj
      (ULiftHom.objUp.{u + 1, u + 1} (Core.mk (familyRankOneLineBundle f M))) ≅
    ((homLift.{u + 1} (FamilyGroupoid.pseudofunctor f)).map
      (familyRankOneInclusion f M).op.toLoc).toFunctor.obj
        (ULiftHom.objUp.{u + 1, u + 1} M) :=
  eqToIso (hobj _ _) ≪≫
    (ULiftHom.up : FamilyGroupoid f (familyRankOneBase f M) ⥤
      ULiftHom.{u + 1} (FamilyGroupoid f (familyRankOneBase f M))).mapIso
        (familyRankOneLineBundleIso f M)

include hobj

/-- Every ambient point against an image line bundle factors through the actual
rank-one open, on the entire slice over every test scheme. -/
lemma coherentRankOneAtlas_points_factor
    (T : Over S) (η : (PicardGroupoid.relativeHomLift f).obj (.mk (op T)))
    (Z : Over T)
    (x : Langlands.CategoryTheory.PseudofunctorPointFiber.Points
      (homLift.{u + 1} (FamilyGroupoid.pseudofunctor f))
      (ULiftHom.objUp.{u + 1, u + 1} M) ((component α T).obj η) Z) :
    ∃ a : Z.left ⟶ familyRankOneBase f M, a ≫ familyRankOneInclusion f M = x.1 := by
  have hN : IsLocallyFreeRankOne
      (ULiftHom.objDown.{u + 1, u + 1} ((component α T).obj η)).of.obj := by
    rw [hobj T η]
    exact (ULiftHom.objDown.{u + 1, u + 1} η).of.property
  exact ⟨familyRankOneHomLiftPointLift f M
      (ULiftHom.objDown.{u + 1, u + 1} ((component α T).obj η)) hN Z x,
    familyRankOneHomLiftPointLift_fac f M
      (ULiftHom.objDown.{u + 1, u + 1} ((component α T).obj η)) hN Z x⟩

include hα

/-- Given the actual coherent inclusion and a locally finite type smooth
coherent-family atlas, its rank-one open is an actual Picard scheme atlas. -/
lemma PicardGroupoid.hasLocallyFiniteTypeSmoothSchemeAtlas_of_coherentAtlas
    (h : Stacks.HasLocallyFiniteTypeSmoothSchemeAtlas
      (homLift.{u + 1} (FamilyGroupoid.pseudofunctor f))) :
    PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas f := by
  obtain ⟨U, ξ, hU, hξ⟩ := h
  let M : FamilyGroupoid f U := ULiftHom.objDown.{u + 1, u + 1} ξ
  let : LocallyOfFiniteType U.hom := hU
  apply (PicardGroupoid.hasLocallyFiniteTypeSmoothSchemeAtlas_homLift_iff f).mp
  exact Stacks.hasLocallyFiniteTypeSmoothSchemeAtlas_of_restrictedAtlas
    α hα (familyRankOneInclusion f M) ξ
    (ULiftHom.objUp.{u + 1, u + 1} (Core.mk (familyRankOneLineBundle f M)))
    (coherentRankOneAtlasImageIso f α hobj M)
    (coherentRankOneAtlas_points_factor f α hobj M)
    (inferInstance) hξ

end Langlands.AlgebraicGeometry.Picard
