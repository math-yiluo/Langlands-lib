import Langlands.Global.AdelicFixedModelInitialSetTopologyStatement
import Langlands.Global.AdelicFixedModelTransitionTopologyProof

/-! # Initial-set independence for the original arithmetic final topologies -/

noncomputable section

universe u

set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable {S U : Finset (AlgebraicCurve.Place k F)} (hSU : S ⊆ U)
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- At a cofinal stage, direct and successive model pullbacks compare homeomorphically. -/
def curvePlaceFixedModelInitialSetStageHomeomorph (V : AdelicLevelIndexAbove U) :
    @Homeomorph
      (RingPoint (curvePlaceSIntegers k F S) X
        (curvePlaceAdeleLevelOver k F S ⟨V.val, hSU.trans V.property⟩))
      (RingPoint (curvePlaceSIntegers k F U) (curvePlaceLevelModelBaseChange k F hSU X)
        (curvePlaceAdeleLevelOver k F U V))
      (curvePlaceFixedModelStageTopology k F S X ⟨V.val, hSU.trans V.property⟩)
      (curvePlaceFixedModelStageTopology k F U (curvePlaceLevelModelBaseChange k F hSU X) V) := by
  let VS : AdelicLevelIndexAbove S := ⟨V.val, hSU.trans V.property⟩
  let US : AdelicLevelIndexAbove S := ⟨U, hSU⟩
  let XU := curvePlaceLevelModelBaseChange k F hSU X
  let := curvePlaceFixedModelStageTopology k F S X VS
  let := curvePlaceFixedModelStageTopology k F U XU V
  let := curvePlaceLevelModelPointTopology k F V.val
    (curvePlaceLevelModelBaseChange k F VS.property X)
  let := curvePlaceLevelModelPointTopology k F V.val
    (curvePlaceLevelModelBaseChange k F V.property XU)
  exact (curvePlaceFixedModelPointHomeomorph k F S X VS).trans
    ((curvePlaceLevelModelIsoHomeomorph k F V.val
      (curvePlaceFixedModelPullbackCompIso k F S X (T := US) (U := VS) V.property)).symm.trans
        (curvePlaceFixedModelPointHomeomorph k F U XU V).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse cofinal comparison is the original model projection on scheme maps. -/
theorem curvePlaceFixedModelInitialSetStageHomeomorph_symm_left
    (V : AdelicLevelIndexAbove U)
    (p : RingPoint (curvePlaceSIntegers k F U) (curvePlaceLevelModelBaseChange k F hSU X)
      (curvePlaceAdeleLevelOver k F U V)) :
    let := curvePlaceFixedModelStageTopology k F S X ⟨V.val, hSU.trans V.property⟩
    let := curvePlaceFixedModelStageTopology k F U (curvePlaceLevelModelBaseChange k F hSU X) V
    ((curvePlaceFixedModelInitialSetStageHomeomorph k F hSU X V).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))) := by
  let := curvePlaceFixedModelStageTopology k F S X ⟨V.val, hSU.trans V.property⟩
  let := curvePlaceFixedModelStageTopology k F U (curvePlaceLevelModelBaseChange k F hSU X) V
  let q := curvePlaceFixedModelPointEquiv k F U (curvePlaceLevelModelBaseChange k F hSU X) V p
  let f := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))
  let g := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F V.property))
  let h := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F (hSU.trans V.property)))
  let e := curvePlaceFixedModelPullbackCompIso k F S X
    (T := ⟨U, hSU⟩) (U := ⟨V.val, hSU.trans V.property⟩) V.property
  have he : e.hom.left ≫ pullback.fst X.hom h =
      pullback.fst (curvePlaceLevelModelBaseChange k F hSU X).hom g ≫ pullback.fst X.hom f :=
    modelPullbackCompIso_hom_left_fst f g h (by rw [← Spec.map_comp]; rfl) X
  have hproj : q.left ≫ pullback.fst (curvePlaceLevelModelBaseChange k F hSU X).hom g = p.left :=
    (curvePlaceFixedModelPointEquiv_symm_left k F U
      (curvePlaceLevelModelBaseChange k F hSU X) V q).symm.trans
      (congrArg (fun r => r.left)
        ((curvePlaceFixedModelPointEquiv k F U
          (curvePlaceLevelModelBaseChange k F hSU X) V).symm_apply_apply p))
  calc
    _ = (q ≫ e.hom).left ≫ pullback.fst X.hom h :=
      curvePlaceFixedModelPointEquiv_symm_left k F S X ⟨V.val, hSU.trans V.property⟩ _
    _ = q.left ≫ (e.hom.left ≫ pullback.fst X.hom h) := Category.assoc _ _ _
    _ = q.left ≫ (pullback.fst (curvePlaceLevelModelBaseChange k F hSU X).hom g ≫
        pullback.fst X.hom f) := congrArg (fun a => q.left ≫ a) he
    _ = (q.left ≫ pullback.fst (curvePlaceLevelModelBaseChange k F hSU X).hom g) ≫
        pullback.fst X.hom f := (Category.assoc _ _ _).symm
    _ = p.left ≫ pullback.fst X.hom f := congrArg (fun a => a ≫ pullback.fst X.hom f) hproj

set_option backward.isDefEq.respectTransparency false in
/-- Cofinal stage comparison commutes with the actual full-adele insertions. -/
theorem curvePlaceFixedModelInitialSetStageHomeomorph_symm_natural
    (V : AdelicLevelIndexAbove U)
    (p : RingPoint (curvePlaceSIntegers k F U) (curvePlaceLevelModelBaseChange k F hSU X)
      (curvePlaceAdeleLevelOver k F U V)) :
    let := curvePlaceFixedModelStageTopology k F S X ⟨V.val, hSU.trans V.property⟩
    let := curvePlaceFixedModelStageTopology k F U (curvePlaceLevelModelBaseChange k F hSU X) V
    (curvePlaceFixedModelInitialSetEquiv k F hSU X).symm
        (p.changeRing (curvePlaceAdeleLevelOverι k F U V).hom) =
      ((curvePlaceFixedModelInitialSetStageHomeomorph k F hSU X V).symm p).changeRing
        (curvePlaceAdeleLevelOverι k F S ⟨V.val, hSU.trans V.property⟩).hom := by
  let := curvePlaceFixedModelStageTopology k F S X ⟨V.val, hSU.trans V.property⟩
  let := curvePlaceFixedModelStageTopology k F U (curvePlaceLevelModelBaseChange k F hSU X) V
  apply RingPoint.ext
  let a := Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevel k F V.val).subtype)
  let f := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU)))
  change ((curvePlaceFixedModelInitialSetEquiv k F hSU X).symm
      (p.changeRing (curvePlaceAdeleLevelOverι k F U V).hom)).left =
    a ≫ ((curvePlaceFixedModelInitialSetStageHomeomorph k F hSU X V).symm p).left
  calc
    _ = (p.changeRing (curvePlaceAdeleLevelOverι k F U V).hom).left ≫ f :=
      curvePlaceFixedModelInitialSetEquiv_symm_left k F hSU X _
    _ = (a ≫ p.left) ≫ f := rfl
    _ = a ≫ (p.left ≫ f) := Category.assoc _ _ _
    _ = a ≫ ((curvePlaceFixedModelInitialSetStageHomeomorph k F hSU X V).symm p).left :=
      congrArg (fun b => a ≫ b)
        (curvePlaceFixedModelInitialSetStageHomeomorph_symm_left k F hSU X V p).symm

/-- The forward cofinal comparison also commutes with the full-adele insertions. -/
theorem curvePlaceFixedModelInitialSetStageHomeomorph_natural
    (V : AdelicLevelIndexAbove U)
    (p : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevelOver k F S ⟨V.val, hSU.trans V.property⟩)) :
    let := curvePlaceFixedModelStageTopology k F S X ⟨V.val, hSU.trans V.property⟩
    let := curvePlaceFixedModelStageTopology k F U (curvePlaceLevelModelBaseChange k F hSU X) V
    curvePlaceFixedModelInitialSetEquiv k F hSU X
        (p.changeRing (curvePlaceAdeleLevelOverι k F S ⟨V.val, hSU.trans V.property⟩).hom) =
      (curvePlaceFixedModelInitialSetStageHomeomorph k F hSU X V p).changeRing
        (curvePlaceAdeleLevelOverι k F U V).hom := by
  let := curvePlaceFixedModelStageTopology k F S X ⟨V.val, hSU.trans V.property⟩
  let := curvePlaceFixedModelStageTopology k F U (curvePlaceLevelModelBaseChange k F hSU X) V
  apply (curvePlaceFixedModelInitialSetEquiv k F hSU X).symm.injective
  rw [Equiv.symm_apply_apply,
    curvePlaceFixedModelInitialSetStageHomeomorph_symm_natural,
    Homeomorph.symm_apply_apply]

end Curve

/-- Initial-set enlargement preserves the original function-field final topology. -/
theorem curvePlaceFixedModelInitialSetTopology :
    CurvePlaceFixedModelInitialSetTopologyStatement.{u} := by
  intro k F _ _ _ _ _ _ S U hSU X _ _
  classical
  let XU := curvePlaceLevelModelBaseChange k F hSU X
  let RS : Type u := curvePlaceSIntegers k F S
  let RU : Type u := curvePlaceSIntegers k F U
  let DS := curvePlaceAdeleLevelOverDiagram k F S
  let DU := curvePlaceAdeleLevelOverDiagram k F U
  let τS := curvePlaceFixedModelStageTopology k F S X
  let τU := curvePlaceFixedModelStageTopology k F U XU
  let cS := curvePlaceAdeleOverCocone k F S
  let cU := curvePlaceAdeleOverCocone k F U
  let : TopologicalSpace (RingPoint RS X cS.pt) :=
    curvePlaceFixedModelAdelePointTopology k F S X
  let : TopologicalSpace (RingPoint RU XU cU.pt) :=
    curvePlaceFixedModelAdelePointTopology k F U XU
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F U XU
  let e := curvePlaceFixedModelInitialSetEquiv k F hSU X
  have hc : Continuous e := by
    apply (ringPointCoconeTopology_continuous_iff RS DS X τS cS e).2
    intro T
    let V : AdelicLevelIndexAbove U := ⟨T.val ∪ U, Finset.subset_union_right⟩
    let VS : AdelicLevelIndexAbove S := ⟨V.val, hSU.trans V.property⟩
    have hTV : T ≤ VS := Finset.subset_union_left
    let : TopologicalSpace (RingPoint RS X (DS.obj T)) := τS T
    let : TopologicalSpace (RingPoint RS X (DS.obj VS)) := τS VS
    let : TopologicalSpace (RingPoint RU XU (DU.obj V)) := τU V
    let h := curvePlaceFixedModelInitialSetStageHomeomorph k F hSU X V
    have htr := (adelicFixedModelTransitionTopology.1 k F S X T VS hTV).1
    have hi := ringPointCoconeTopology_continuous_ι RU DU XU τU cU V
    have hcomp := hi.comp (h.continuous.comp htr)
    have hn :
        (fun p : RingPoint RS X (DS.obj T) =>
          (h (p.changeRing (curvePlaceAdeleLevelOverMap k F S hTV).hom)).changeRing
            (curvePlaceAdeleLevelOverι k F U V).hom) =
        (e ∘ fun p : RingPoint RS X (DS.obj T) =>
          p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom) := by
      funext p
      rw [← curvePlaceFixedModelInitialSetStageHomeomorph_natural]
      apply congrArg e
      exact ConcreteCategory.congr_hom ((ringPointCocone RS DS X cS).w (homOfLE hTV)) p
    change Continuous (fun p : RingPoint RS X (DS.obj T) =>
      (h (p.changeRing (curvePlaceAdeleLevelOverMap k F S hTV).hom)).changeRing
        (curvePlaceAdeleLevelOverι k F U V).hom) at hcomp
    rwa [hn] at hcomp
  have hi : Continuous e.symm := by
    apply (ringPointCoconeTopology_continuous_iff RU DU XU τU cU e.symm).2
    intro V
    let VS : AdelicLevelIndexAbove S := ⟨V.val, hSU.trans V.property⟩
    let : TopologicalSpace (RingPoint RS X (DS.obj VS)) := τS VS
    let : TopologicalSpace (RingPoint RU XU (DU.obj V)) := τU V
    let h := curvePlaceFixedModelInitialSetStageHomeomorph k F hSU X V
    have hiS := ringPointCoconeTopology_continuous_ι RS DS X τS cS VS
    have hcomp := hiS.comp h.symm.continuous
    have hn :
        (fun p : RingPoint RU XU (DU.obj V) =>
          (h.symm p).changeRing (curvePlaceAdeleLevelOverι k F S VS).hom) =
        (e.symm ∘ fun p : RingPoint RU XU (DU.obj V) =>
          p.changeRing (curvePlaceAdeleLevelOverι k F U V).hom) := by
      funext p
      exact (curvePlaceFixedModelInitialSetStageHomeomorph_symm_natural k F hSU X V p).symm
    change Continuous (fun p : RingPoint RU XU (DU.obj V) =>
      (h.symm p).changeRing (curvePlaceAdeleLevelOverι k F S VS).hom) at hcomp
    rwa [hn] at hcomp
  exact ({ toEquiv := e, continuous_toFun := hc, continuous_invFun := hi } :
    CurvePlaceFixedModelAdelePoints k F S X ≃ₜ CurvePlaceFixedModelAdelePoints k F U XU).isHomeomorph

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable {S U : Finset (FinitePlace K)} (hSU : S ⊆ U)
variable (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))

/-- At a cofinal stage, direct and successive model pullbacks compare homeomorphically. -/
def numberFieldFixedModelInitialSetStageHomeomorph (V : AdelicLevelIndexAbove U) :
    @Homeomorph
      (RingPoint (((S : Set (FinitePlace K)).integer K)) X
        (numberFieldAdeleLevelOver K S ⟨V.val, hSU.trans V.property⟩))
      (RingPoint (((U : Set (FinitePlace K)).integer K)) (numberFieldLevelModelBaseChange K hSU X)
        (numberFieldAdeleLevelOver K U V))
      (numberFieldFixedModelStageTopology K S X ⟨V.val, hSU.trans V.property⟩)
      (numberFieldFixedModelStageTopology K U (numberFieldLevelModelBaseChange K hSU X) V) := by
  let VS : AdelicLevelIndexAbove S := ⟨V.val, hSU.trans V.property⟩
  let US : AdelicLevelIndexAbove S := ⟨U, hSU⟩
  let XU := numberFieldLevelModelBaseChange K hSU X
  let := numberFieldFixedModelStageTopology K S X VS
  let := numberFieldFixedModelStageTopology K U XU V
  let := numberFieldLevelModelPointTopology K V.val
    (numberFieldLevelModelBaseChange K VS.property X)
  let := numberFieldLevelModelPointTopology K V.val
    (numberFieldLevelModelBaseChange K V.property XU)
  exact (numberFieldFixedModelPointHomeomorph K S X VS).trans
    ((numberFieldLevelModelIsoHomeomorph K V.val
      (numberFieldFixedModelPullbackCompIso K S X (T := US) (U := VS) V.property)).symm.trans
        (numberFieldFixedModelPointHomeomorph K U XU V).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse cofinal comparison is the original model projection on scheme maps. -/
theorem numberFieldFixedModelInitialSetStageHomeomorph_symm_left
    (V : AdelicLevelIndexAbove U)
    (p : RingPoint (((U : Set (FinitePlace K)).integer K)) (numberFieldLevelModelBaseChange K hSU X)
      (numberFieldAdeleLevelOver K U V)) :
    let := numberFieldFixedModelStageTopology K S X ⟨V.val, hSU.trans V.property⟩
    let := numberFieldFixedModelStageTopology K U (numberFieldLevelModelBaseChange K hSU X) V
    ((numberFieldFixedModelInitialSetStageHomeomorph K hSU X V).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))) := by
  let := numberFieldFixedModelStageTopology K S X ⟨V.val, hSU.trans V.property⟩
  let := numberFieldFixedModelStageTopology K U (numberFieldLevelModelBaseChange K hSU X) V
  let q := numberFieldFixedModelPointEquiv K U (numberFieldLevelModelBaseChange K hSU X) V p
  let f := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))
  let g := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K V.property))
  let h := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K (hSU.trans V.property)))
  let e := numberFieldFixedModelPullbackCompIso K S X
    (T := ⟨U, hSU⟩) (U := ⟨V.val, hSU.trans V.property⟩) V.property
  have he : e.hom.left ≫ pullback.fst X.hom h =
      pullback.fst (numberFieldLevelModelBaseChange K hSU X).hom g ≫ pullback.fst X.hom f :=
    modelPullbackCompIso_hom_left_fst f g h (by rw [← Spec.map_comp]; rfl) X
  have hproj : q.left ≫ pullback.fst (numberFieldLevelModelBaseChange K hSU X).hom g = p.left :=
    (numberFieldFixedModelPointEquiv_symm_left K U
      (numberFieldLevelModelBaseChange K hSU X) V q).symm.trans
      (congrArg (fun r => r.left)
        ((numberFieldFixedModelPointEquiv K U
          (numberFieldLevelModelBaseChange K hSU X) V).symm_apply_apply p))
  calc
    _ = (q ≫ e.hom).left ≫ pullback.fst X.hom h :=
      numberFieldFixedModelPointEquiv_symm_left K S X ⟨V.val, hSU.trans V.property⟩ _
    _ = q.left ≫ (e.hom.left ≫ pullback.fst X.hom h) := Category.assoc _ _ _
    _ = q.left ≫ (pullback.fst (numberFieldLevelModelBaseChange K hSU X).hom g ≫
        pullback.fst X.hom f) := congrArg (fun a => q.left ≫ a) he
    _ = (q.left ≫ pullback.fst (numberFieldLevelModelBaseChange K hSU X).hom g) ≫
        pullback.fst X.hom f := (Category.assoc _ _ _).symm
    _ = p.left ≫ pullback.fst X.hom f := congrArg (fun a => a ≫ pullback.fst X.hom f) hproj

set_option backward.isDefEq.respectTransparency false in
/-- Cofinal stage comparison commutes with the actual full-adele insertions. -/
theorem numberFieldFixedModelInitialSetStageHomeomorph_symm_natural
    (V : AdelicLevelIndexAbove U)
    (p : RingPoint (((U : Set (FinitePlace K)).integer K)) (numberFieldLevelModelBaseChange K hSU X)
      (numberFieldAdeleLevelOver K U V)) :
    let := numberFieldFixedModelStageTopology K S X ⟨V.val, hSU.trans V.property⟩
    let := numberFieldFixedModelStageTopology K U (numberFieldLevelModelBaseChange K hSU X) V
    (numberFieldFixedModelInitialSetEquiv K hSU X).symm
        (p.changeRing (numberFieldAdeleLevelOverι K U V).hom) =
      ((numberFieldFixedModelInitialSetStageHomeomorph K hSU X V).symm p).changeRing
        (numberFieldAdeleLevelOverι K S ⟨V.val, hSU.trans V.property⟩).hom := by
  let := numberFieldFixedModelStageTopology K S X ⟨V.val, hSU.trans V.property⟩
  let := numberFieldFixedModelStageTopology K U (numberFieldLevelModelBaseChange K hSU X) V
  apply RingPoint.ext
  let a := Spec.map (CommRingCat.ofHom (numberFieldAdeleLevel K V.val).subtype)
  let f := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU)))
  change ((numberFieldFixedModelInitialSetEquiv K hSU X).symm
      (p.changeRing (numberFieldAdeleLevelOverι K U V).hom)).left =
    a ≫ ((numberFieldFixedModelInitialSetStageHomeomorph K hSU X V).symm p).left
  calc
    _ = (p.changeRing (numberFieldAdeleLevelOverι K U V).hom).left ≫ f :=
      numberFieldFixedModelInitialSetEquiv_symm_left K hSU X _
    _ = (a ≫ p.left) ≫ f := rfl
    _ = a ≫ (p.left ≫ f) := Category.assoc _ _ _
    _ = a ≫ ((numberFieldFixedModelInitialSetStageHomeomorph K hSU X V).symm p).left :=
      congrArg (fun b => a ≫ b)
        (numberFieldFixedModelInitialSetStageHomeomorph_symm_left K hSU X V p).symm

/-- The forward cofinal comparison also commutes with the full-adele insertions. -/
theorem numberFieldFixedModelInitialSetStageHomeomorph_natural
    (V : AdelicLevelIndexAbove U)
    (p : RingPoint (((S : Set (FinitePlace K)).integer K)) X
      (numberFieldAdeleLevelOver K S ⟨V.val, hSU.trans V.property⟩)) :
    let := numberFieldFixedModelStageTopology K S X ⟨V.val, hSU.trans V.property⟩
    let := numberFieldFixedModelStageTopology K U (numberFieldLevelModelBaseChange K hSU X) V
    numberFieldFixedModelInitialSetEquiv K hSU X
        (p.changeRing (numberFieldAdeleLevelOverι K S ⟨V.val, hSU.trans V.property⟩).hom) =
      (numberFieldFixedModelInitialSetStageHomeomorph K hSU X V p).changeRing
        (numberFieldAdeleLevelOverι K U V).hom := by
  let := numberFieldFixedModelStageTopology K S X ⟨V.val, hSU.trans V.property⟩
  let := numberFieldFixedModelStageTopology K U (numberFieldLevelModelBaseChange K hSU X) V
  apply (numberFieldFixedModelInitialSetEquiv K hSU X).symm.injective
  rw [Equiv.symm_apply_apply,
    numberFieldFixedModelInitialSetStageHomeomorph_symm_natural,
    Homeomorph.symm_apply_apply]

end NumberField

/-- Initial-set enlargement preserves the original full number-field final topology. -/
theorem numberFieldFixedModelInitialSetTopology :
    NumberFieldFixedModelInitialSetTopologyStatement.{u} := by
  intro K _ _ S U hSU X _ _
  classical
  let XU := numberFieldLevelModelBaseChange K hSU X
  let RS : Type u := ((S : Set (FinitePlace K)).integer K)
  let RU : Type u := ((U : Set (FinitePlace K)).integer K)
  let DS := numberFieldAdeleLevelOverDiagram K S
  let DU := numberFieldAdeleLevelOverDiagram K U
  let τS := numberFieldFixedModelStageTopology K S X
  let τU := numberFieldFixedModelStageTopology K U XU
  let cS := numberFieldAdeleOverCocone K S
  let cU := numberFieldAdeleOverCocone K U
  let : TopologicalSpace (RingPoint RS X cS.pt) :=
    numberFieldFixedModelAdelePointTopology K S X
  let : TopologicalSpace (RingPoint RU XU cU.pt) :=
    numberFieldFixedModelAdelePointTopology K U XU
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K U XU
  let e := numberFieldFixedModelInitialSetEquiv K hSU X
  have hc : Continuous e := by
    apply (ringPointCoconeTopology_continuous_iff RS DS X τS cS e).2
    intro T
    let V : AdelicLevelIndexAbove U := ⟨T.val ∪ U, Finset.subset_union_right⟩
    let VS : AdelicLevelIndexAbove S := ⟨V.val, hSU.trans V.property⟩
    have hTV : T ≤ VS := Finset.subset_union_left
    let : TopologicalSpace (RingPoint RS X (DS.obj T)) := τS T
    let : TopologicalSpace (RingPoint RS X (DS.obj VS)) := τS VS
    let : TopologicalSpace (RingPoint RU XU (DU.obj V)) := τU V
    let h := numberFieldFixedModelInitialSetStageHomeomorph K hSU X V
    have htr := (adelicFixedModelTransitionTopology.2 K S X T VS hTV).1
    have hi := ringPointCoconeTopology_continuous_ι RU DU XU τU cU V
    have hcomp := hi.comp (h.continuous.comp htr)
    have hn :
        (fun p : RingPoint RS X (DS.obj T) =>
          (h (p.changeRing (numberFieldAdeleLevelOverMap K S hTV).hom)).changeRing
            (numberFieldAdeleLevelOverι K U V).hom) =
        (e ∘ fun p : RingPoint RS X (DS.obj T) =>
          p.changeRing (numberFieldAdeleLevelOverι K S T).hom) := by
      funext p
      rw [← numberFieldFixedModelInitialSetStageHomeomorph_natural]
      apply congrArg e
      exact ConcreteCategory.congr_hom ((ringPointCocone RS DS X cS).w (homOfLE hTV)) p
    change Continuous (fun p : RingPoint RS X (DS.obj T) =>
      (h (p.changeRing (numberFieldAdeleLevelOverMap K S hTV).hom)).changeRing
        (numberFieldAdeleLevelOverι K U V).hom) at hcomp
    rwa [hn] at hcomp
  have hi : Continuous e.symm := by
    apply (ringPointCoconeTopology_continuous_iff RU DU XU τU cU e.symm).2
    intro V
    let VS : AdelicLevelIndexAbove S := ⟨V.val, hSU.trans V.property⟩
    let : TopologicalSpace (RingPoint RS X (DS.obj VS)) := τS VS
    let : TopologicalSpace (RingPoint RU XU (DU.obj V)) := τU V
    let h := numberFieldFixedModelInitialSetStageHomeomorph K hSU X V
    have hiS := ringPointCoconeTopology_continuous_ι RS DS X τS cS VS
    have hcomp := hiS.comp h.symm.continuous
    have hn :
        (fun p : RingPoint RU XU (DU.obj V) =>
          (h.symm p).changeRing (numberFieldAdeleLevelOverι K S VS).hom) =
        (e.symm ∘ fun p : RingPoint RU XU (DU.obj V) =>
          p.changeRing (numberFieldAdeleLevelOverι K U V).hom) := by
      funext p
      exact (numberFieldFixedModelInitialSetStageHomeomorph_symm_natural K hSU X V p).symm
    change Continuous (fun p : RingPoint RU XU (DU.obj V) =>
      (h.symm p).changeRing (numberFieldAdeleLevelOverι K S VS).hom) at hcomp
    rwa [hn] at hcomp
  exact ({ toEquiv := e, continuous_toFun := hc, continuous_invFun := hi } :
    NumberFieldFixedModelAdelePoints K S X ≃ₜ NumberFieldFixedModelAdelePoints K U XU).isHomeomorph

/-- The exact initial-set topology target in both arithmetic settings. -/
theorem adelicFixedModelInitialSetTopology : AdelicFixedModelInitialSetTopologyStatement.{u} :=
  ⟨curvePlaceFixedModelInitialSetTopology, numberFieldFixedModelInitialSetTopology⟩

end Langlands.Global
