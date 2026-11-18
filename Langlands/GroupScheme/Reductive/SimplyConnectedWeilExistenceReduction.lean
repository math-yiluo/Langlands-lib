import Langlands.GroupScheme.Reductive.RootComponentDerivedComparison
import Langlands.GroupScheme.Reductive.RootComponentFieldProduct
import Langlands.GroupScheme.Reductive.EtalePinnedComparison
import Langlands.GroupScheme.Reductive.SimplyConnectedWeilPresentation
import Langlands.GroupScheme.Reductive.FiniteProducts

/-! # Simply connected affine Weil existence from split isomorphism and pair descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- A finite product of reductive groups is reductive over an arbitrary base. -/
theorem isReductive_pi {S : Scheme.{u}} {I : Type u} [Finite I]
    (F : I → GroupScheme S) (hF : ∀ i, IsReductive (F i)) : IsReductive (pi F) := by
  let : MorphismProperty.ContainsIdentities (@Smooth : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  refine ⟨prop_pi_hom @Smooth F (fun i => (hF i).smooth),
    prop_pi_hom @IsAffineHom F (fun i => (hF i).isAffineHom), ?_⟩
  intro s
  have hp : IsConnectedReductive (pi (fun i => geometricFiber (F i) s)) :=
    isConnectedReductive_pi_of_isAlgClosed _
      (fun i => ((hF i).geometricFiber s).isConnectedReductive_of_isAlgClosed)
  exact hp.isPseudoReductive.of_iso
    (PreservesProduct.iso (baseChange (geometricPoint S s)) F)

namespace RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

local instance : Smooth M.group.X.hom := M.reductive.smooth

/-- Every simply connected algebraically closed field fibre of the pinned
model is the actual product of the relative derived component fibres. -/
def componentDerivedProductFieldIso
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra M.ring K]
    (hsc : IsSimplyConnected ((baseChange (algebraBaseMap M.ring K)).obj M.group)) :
    (baseChange (algebraBaseMap M.ring K)).obj M.group ≅
      (baseChange (algebraBaseMap M.ring K)).obj (pi D.componentDerivedGroup) := by
  let N := fun c => D.fieldComponentNormalModel K hsc.isSemisimple c
  exact (D.componentNormalProductIso_of_isSimplyConnected K N hsc).symm ≪≫
    Pi.mapIso (fun c => D.fieldComponentDerivedIso c K (N c)) ≪≫
      (PreservesProduct.iso (baseChange (algebraBaseMap M.ring K)) D.componentDerivedGroup).symm

/-- Assuming affine split classification, a pinned model with simply connected
geometric fibres has actual étale-local comparisons with its relative product. -/
def componentDerivedProductComparisonAtlas
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (hsc : IsFibrewiseSimplyConnected M.group) :
    AffineComparisonAtlas M.group (pi D.componentDerivedGroup) := by
  apply AffineComparisonAtlas.ofPinnedFieldIso hAffine M (pi D.componentDerivedGroup)
    (isReductive_pi _ D.componentDerivedGroup_reductive)
  intro K _ _ b
  let : Algebra M.ring K := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap M.ring K = b := Spec.map_preimage b
  have hfield : IsSimplyConnected ((baseChange (algebraBaseMap M.ring K)).obj M.group) := by
    rw [hb]
    exact (fieldSimplyConnected_iff_geometricFiber M.group b).mpr (hsc _)
  have e := D.componentDerivedProductFieldIso K hfield
  rw [hb] at e
  exact ⟨e⟩

/-- All relative component candidates have almost-simple geometric fibres
after an arbitrary base change, under simply connected ambient fibres. -/
theorem componentDerivedGroup_baseChange_almostSimple
    (hsc : IsFibrewiseSimplyConnected M.group)
    {T : Scheme.{u}} (b : T ⟶ M.base) (c : Component M.basis) (t : T) :
    IsAlmostSimple (geometricFiber ((baseChange b).obj (D.componentDerivedGroup c)) t) := by
  let K := AlgebraicClosure (T.residueField t)
  let q := geometricPoint T t ≫ b
  let : Algebra M.ring K := (Spec.preimage q).hom.toAlgebra
  have hq : algebraBaseMap M.ring K = q := Spec.map_preimage q
  have hfield : IsSimplyConnected ((baseChange q).obj M.group) :=
    (fieldSimplyConnected_iff_geometricFiber M.group q).mpr (hsc _)
  have hAS := D.componentDerivedGroup_isAlmostSimple_field c K
    (show IsSemisimple ((baseChange (algebraBaseMap M.ring K)).obj M.group) from by
      rw [hq]
      exact hfield.isSemisimple)
  rw [hq] at hAS
  exact hAS.of_iso (baseChangeCompIso b (geometricPoint T t) (D.componentDerivedGroup c)).symm

end RootComponentCoordinates

namespace AffineSimplyConnectedWeilPresentation

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

/-- Actual affine simply connected Weil existence for a supplied pinned
model, conditional only on affine split isomorphism and generic pair descent. -/
def ofPinnedModel
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (hD : AffineWeilPairEtaleDescentStatement.{u})
    (M : AffineSimplyConnectedPinnedModel.{u})
    (hnt : HasNontrivialGeometricFibres M.group) :
    AffineSimplyConnectedWeilPresentation M.group := by
  let D := M.rootComponentCoordinates
  let C := D.componentDerivedProductComparisonAtlas hAffine M.isFibrewiseSimplyConnected
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
      AffineSimplyConnectedWeilPresentation
        ((baseChange (algebraBaseMap M.ring (R s))).obj M.group) :=
    ofProduct (F s) (e s) (hnt.baseChange _) (fun c =>
      (D.componentDerivedGroup_reductive c).baseChange _) (fun c =>
      (D.componentDerivedGroup_simplyConnected M.isFibrewiseSimplyConnected c).baseChange _)
      (fun c t => D.componentDerivedGroup_baseChange_almostSimple M.isFibrewiseSimplyConnected _ c t)
  let : IsAffine M.group.X.left :=
    @isAffine_of_isAffineHom _ _ M.group.X.hom M.reductive.isAffineHom inferInstance
  let : Smooth M.group.X.hom := M.reductive.smooth
  let : LocallyOfFiniteType M.group.X.hom := inferInstance
  apply ofEtaleLocal hD M.group R P
  intro s
  refine ⟨s, C.point s, ?_⟩
  rw [hb s]
  exact C.image_point s


/-- Arbitrary affine simply connected Weil existence from the two explicit
structural inputs, using the actual pinned étale atlas of the original group. -/
def ofReductive
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (hD : AffineWeilPairEtaleDescentStatement.{u})
    {A : Type u} [CommRing A] (G : GroupScheme (Spec (CommRingCat.of A)))
    (hG : IsReductive G) (hsc : IsFibrewiseSimplyConnected G)
    (hnt : HasNontrivialGeometricFibres G) : AffineSimplyConnectedWeilPresentation G := by
  classical
  let C := AffinePinnedAtlas.ofReductive hG
  have hmodelSC (s : Spec (CommRingCat.of A)) :
      IsFibrewiseSimplyConnected (C.chart s).model.group := by
    intro t
    exact ((hsc.baseChange (C.chart s).map) t).of_iso
      ((baseChange (geometricPoint _ t)).mapIso (C.chart s).iso).symm
  let M (s : Spec (CommRingCat.of A)) : AffineSimplyConnectedPinnedModel :=
    { toAffinePinnedModel := (C.chart s).model
      corootSpan_eq_top := ((C.chart s).model.isSimplyConnected_geometricFiber_iff
        (C.point s)).mp (hmodelSC s (C.point s)) }
  have hmodelNT (s : Spec (CommRingCat.of A)) : HasNontrivialGeometricFibres (M s).group := by
    intro t
    exact (hasNontrivialPoints_iff_of_iso
      ((baseChange (geometricPoint _ t)).mapIso (C.chart s).iso)).mp
      ((hnt.baseChange (C.chart s).map) t)
  let R (s : Spec (CommRingCat.of A)) := (C.chart s).model.ring
  let : ∀ s, CommRing (R s) := fun s => (C.chart s).model.commRing
  let : ∀ s, Algebra A (R s) := fun s => (Spec.preimage (C.chart s).map).hom.toAlgebra
  have hb (s : Spec (CommRingCat.of A)) :
      algebraBaseMap A (R s) = (C.chart s).map := Spec.map_preimage (C.chart s).map
  let : ∀ s, Algebra.Etale A (R s) := fun s => by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    change Etale (algebraBaseMap A (R s))
    rw [hb s]
    exact (C.chart s).etale
  let P (s : Spec (CommRingCat.of A)) : AffineSimplyConnectedWeilPresentation
      ((baseChange (algebraBaseMap A (R s))).obj G) :=
    (ofPinnedModel hAffine hD (M s) (hmodelNT s)).precompose
      (eqToIso (congrArg (fun b => (baseChange b).obj G) (hb s)) ≪≫ (C.chart s).iso)
  let : IsAffine G.X.left := @isAffine_of_isAffineHom _ _ G.X.hom hG.isAffineHom inferInstance
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  apply ofEtaleLocal hD G R P
  intro s
  refine ⟨s, C.point s, ?_⟩
  rw [hb s]
  exact C.image_point s

end AffineSimplyConnectedWeilPresentation

end Langlands.GroupScheme
