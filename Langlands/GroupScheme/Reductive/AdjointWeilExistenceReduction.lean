import Langlands.GroupScheme.Reductive.RootComponentDerivedComparison
import Langlands.GroupScheme.Reductive.RootComponentFieldProduct
import Langlands.GroupScheme.Reductive.EtalePinnedComparison
import Langlands.GroupScheme.Reductive.AdjointWeilDescentReduction
import Langlands.GroupScheme.Reductive.AdjointRootComponentCoordinates
import Langlands.GroupScheme.Reductive.FiniteProducts

/-! # Adjoint affine Weil existence from split isomorphism and pair descent -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

private local instance : Smooth M.group.X.hom := M.reductive.smooth

private theorem componentDerivedProduct_reductive : IsReductive (pi D.componentDerivedGroup) := by
  let : MorphismProperty.ContainsIdentities (@Smooth : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  refine ⟨prop_pi_hom @Smooth D.componentDerivedGroup
      (fun c => (D.componentDerivedGroup_reductive c).smooth),
    prop_pi_hom @IsAffineHom D.componentDerivedGroup
      (fun c => (D.componentDerivedGroup_reductive c).isAffineHom), ?_⟩
  intro s
  have hp : IsConnectedReductive (pi (fun c => geometricFiber (D.componentDerivedGroup c) s)) :=
    isConnectedReductive_pi_of_isAlgClosed _ (fun c =>
      ((D.componentDerivedGroup_reductive c).geometricFiber s).isConnectedReductive_of_isAlgClosed)
  exact hp.isPseudoReductive.of_iso
    (PreservesProduct.iso (baseChange (geometricPoint M.base s)) D.componentDerivedGroup)

/-- Every adjoint algebraically closed field fibre of the pinned
model is the actual product of the relative derived component fibres. -/
def componentDerivedProductFieldIso_of_isAdjoint
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra M.ring K]
    (hadj : IsAdjoint ((baseChange (algebraBaseMap M.ring K)).obj M.group)) :
    (baseChange (algebraBaseMap M.ring K)).obj M.group ≅
      (baseChange (algebraBaseMap M.ring K)).obj (pi D.componentDerivedGroup) := by
  let N := fun c => D.fieldComponentNormalModel K hadj.isSemisimple c
  exact (D.componentNormalProductIso_of_isAdjoint K N hadj).symm ≪≫
    Pi.mapIso (fun c => D.fieldComponentDerivedIso c K (N c)) ≪≫
      (PreservesProduct.iso (baseChange (algebraBaseMap M.ring K)) D.componentDerivedGroup).symm

/-- Assuming affine split classification, a pinned model with adjoint
geometric fibres has actual étale-local comparisons with its relative product. -/
def componentDerivedProductComparisonAtlas_of_isAdjoint
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (hadj : IsFibrewiseAdjoint M.group) :
    AffineComparisonAtlas M.group (pi D.componentDerivedGroup) := by
  apply AffineComparisonAtlas.ofPinnedFieldIso hAffine M (pi D.componentDerivedGroup)
    (componentDerivedProduct_reductive D)
  intro K _ _ b
  let : Algebra M.ring K := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap M.ring K = b := Spec.map_preimage b
  have hfield : IsAdjoint ((baseChange (algebraBaseMap M.ring K)).obj M.group) := by
    rw [hb]
    exact (fieldAdjoint_iff_geometricFiber M.group b).mpr (hadj _)
  have e := D.componentDerivedProductFieldIso_of_isAdjoint K hfield
  rw [hb] at e
  exact ⟨e⟩

/-- All relative component candidates have almost-simple geometric fibres
after an arbitrary base change, under adjoint ambient fibres. -/
theorem componentDerivedGroup_baseChange_almostSimple_of_isAdjoint
    (hadj : IsFibrewiseAdjoint M.group)
    {T : Scheme.{u}} (b : T ⟶ M.base) (c : Component M.basis) (t : T) :
    IsAlmostSimple (geometricFiber ((baseChange b).obj (D.componentDerivedGroup c)) t) := by
  let K := AlgebraicClosure (T.residueField t)
  let q := geometricPoint T t ≫ b
  let : Algebra M.ring K := (Spec.preimage q).hom.toAlgebra
  have hq : algebraBaseMap M.ring K = q := Spec.map_preimage q
  have hfield : IsAdjoint ((baseChange q).obj M.group) :=
    (fieldAdjoint_iff_geometricFiber M.group q).mpr (hadj _)
  have hAS := D.componentDerivedGroup_isAlmostSimple_field c K
    (show IsSemisimple ((baseChange (algebraBaseMap M.ring K)).obj M.group) from by
      rw [hq]
      exact hfield.isSemisimple)
  rw [hq] at hAS
  exact hAS.of_iso (baseChangeCompIso b (geometricPoint T t) (D.componentDerivedGroup c)).symm

end RootComponentCoordinates

namespace AffineAdjointWeilPresentation

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

/-- An actual adjoint Weil presentation of a supplied pinned model, from
actual field products, further étale comparison and generic pair descent. -/
def ofPinnedModel
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (hD : AffineWeilPairEtaleDescentStatement.{u})
    (M : AffineAdjointPinnedModel.{u}) (hnt : IsFibrewiseNontrivial M.group) :
    AffineAdjointWeilPresentation M.group := by
  let D := M.toAffinePinnedModel.adjointRootComponentCoordinates M.rootSpan_eq_top
  let C := D.componentDerivedProductComparisonAtlas_of_isAdjoint hAffine M.isFibrewiseAdjoint
  let R (s : M.toAffinePinnedModel.base) := (C.chart s).ring
  let : ∀ s, CommRing (R s) := fun s => (C.chart s).commRing
  let : ∀ s, Algebra M.ring (R s) := fun s => (Spec.preimage (C.chart s).map).hom.toAlgebra
  have hb (s : M.toAffinePinnedModel.base) :
      algebraBaseMap M.ring (R s) = (C.chart s).map := Spec.map_preimage (C.chart s).map
  let : ∀ s, Algebra.Etale M.ring (R s) := fun s => by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    change Etale (algebraBaseMap M.ring (R s))
    rw [hb s]
    exact (C.chart s).etale
  let F (s : M.toAffinePinnedModel.base) (c : Component M.basis) :
      GroupScheme (Spec (CommRingCat.of (R s))) :=
    (baseChange (algebraBaseMap M.ring (R s))).obj (D.componentDerivedGroup c)
  let e (s : M.toAffinePinnedModel.base) :
      (baseChange (algebraBaseMap M.ring (R s))).obj M.group ≅ pi (F s) :=
    eqToIso (congrArg (fun b => (baseChange b).obj M.group) (hb s)) ≪≫ (C.chart s).iso ≪≫
      (eqToIso (congrArg (fun b => (baseChange b).obj (pi D.componentDerivedGroup))
        (hb s))).symm ≪≫
      PreservesProduct.iso (baseChange (algebraBaseMap M.ring (R s))) D.componentDerivedGroup
  let P (s : M.toAffinePinnedModel.base) :
      AffineAdjointWeilPresentation
        ((baseChange (algebraBaseMap M.ring (R s))).obj M.group) :=
    ofProduct (F s) (e s) (center_eq_bot_baseChange _ M.center_eq_bot) (hnt.baseChange _)
      (fun c => (D.componentDerivedGroup_reductive c).baseChange _)
      (fun c t => D.componentDerivedGroup_baseChange_almostSimple_of_isAdjoint
        M.isFibrewiseAdjoint _ c t)
  let : IsAffine M.group.X.left :=
    @isAffine_of_isAffineHom _ _ M.group.X.hom M.reductive.isAffineHom inferInstance
  let : Smooth M.group.X.hom := M.reductive.smooth
  let : LocallyOfFiniteType M.group.X.hom := inferInstance
  apply ofEtaleLocal hD M.group R P
  intro s
  refine ⟨s, C.point s, ?_⟩
  rw [hb s]
  exact C.image_point s

end AffineAdjointWeilPresentation
end Langlands.GroupScheme
