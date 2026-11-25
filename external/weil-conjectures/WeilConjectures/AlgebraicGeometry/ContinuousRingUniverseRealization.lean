/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.Topology.ContinuousMapCondensedRing
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation

/-!
# Continuous coefficient realization in the scheme universe

Source: Hemo--Richarz--Scholbach, Example 3.1. This is the canonical adjoint
comparison, extending the existing Type 0 ring realization to Type u.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj

namespace AlgebraicGeometry.ProEtale.ContinuousRingUniverse

/-- Naturality of the projection from a profinite test scheme.
Source: HRS Example 3.1; the canonical test projection.
(auxiliary; not a blueprint node) -/
theorem testProjection_natural (X : Scheme.{u}) {S T : Profinite.{u}} (f : S ⟶ T) :
    (profiniteTestProjection X T).comp ((profiniteToProEtOf X).map f).left.base.hom =
      f.hom.hom.comp (profiniteTestProjection X S) := by
  exact profiniteTestProjection_natural X f

/-- The adjoint comparison given by precomposing a continuous function with the test projection.
Source: HRS Example 3.1; the point-Lan affine evaluation proof.
(auxiliary; not a blueprint node) -/
noncomputable def comparisonAdjoint (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    Profinite.continuousMapRingObjOfUniverse E ⟶
      (pointLowerStar.obj ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousCoefficientRingSheaf X E)))) :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ULift.up (f.down.comp (profiniteTestProjection X S.unop))
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [testProjection_natural] }⟩

/-- The canonical continuous-ring realization, defined by the point inverse-image adjunction.
Source: HRS Example 3.1; the point-Lan affine evaluation proof.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def comparison (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    condensedRingObj (Profinite.continuousMapRingObjOfUniverse E) X ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousCoefficientRingSheaf X E)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).symm
      (comparisonAdjoint X E)

private lemma comparison_eq (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    (S : Profinite.{u}) (f : C(S, E)) :
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _
        (comparison X E)).hom.app (Opposite.op S)) (ULift.up f) =
          ULift.up (f.comp (profiniteTestProjection X S)) := by
  rw [comparison, Equiv.apply_symm_apply]
  rfl

private noncomputable def comparisonAdjointRing (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    Profinite.continuousMapRingSheafOfUniverse E ⟶
      (profiniteToProEt.sheafPushforwardContinuous RingCat.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).obj
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)).obj
            (continuousCoefficientRingSheaf X E)) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ContinuousMap.compRightAlgHom ℤ E (profiniteTestProjection X S.unop)).toRingHom).comp
            ULift.ringEquiv.toRingHom))
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

private lemma comparisonAdjoint_isMonHom (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    IsMonHom (comparisonAdjoint X E) := by
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology specZ.{u}
  let L := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X E
  have h₁ := pushforwardRingMonObj F K L R
  have h₂ := pushforwardRingMonObj profiniteToProEt J K
    ((F.sheafPushforwardContinuous RingCat.{u + 1} K L).obj R)
  change @IsMonHom _ _ _ _ _ _
    ((profiniteToProEt.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).monObjObj
      (((F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} K L).obj
        ((sheafCompose L (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R)))) _
  erw [← h₁, ← h₂]
  exact Sheaf.isMonHom_sheafCompose_map J (comparisonAdjointRing X E)

/-- The canonical realization preserves the internal ring operations.
Source: HRS Example 3.1; the point-Lan affine evaluation proof.
(auxiliary; not a blueprint node) -/
instance comparison_isMonHom (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    IsMonHom (comparison X E) := by
  have := comparisonAdjoint_isMonHom X E
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let f : Mon.mk (Profinite.continuousMapRingObjOfUniverse E) ⟶
      ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)) ⋙ pointLowerStar).mapMon.obj
        (Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousCoefficientRingSheaf X E))) := Mon.ofHom (comparisonAdjoint X E)
  let g := (a.mapMon.homEquiv _ _).symm f
  unfold comparison
  change IsMonHom g.hom
  exact g.isMonHom_hom

private noncomputable def kanComparison (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    (profiniteToProEtOf X).op.lan.obj (Profinite.continuousMapRingObjOfUniverse E).obj ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousCoefficientRingSheaf X E)).obj :=
  (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (comparisonAdjoint X E).hom

private lemma kanComparison_unit (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    (profiniteToProEtOf X).op.lanUnit.app (Profinite.continuousMapRingObjOfUniverse E).obj ≫
      Functor.whiskerLeft (profiniteToProEtOf X).op (kanComparison X E) =
        (comparisonAdjoint X E).hom := by
  have h := (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv
    (Profinite.continuousMapRingObjOfUniverse E).obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf X E)).obj).apply_symm_apply (comparisonAdjoint X E).hom
  dsimp only [kanComparison]
  rw [← Functor.lanAdjunction_unit]
  exact h

private lemma kanComparison_isIso (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (wU : PointLanWeaklyContractible X U)
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (η : (Profinite.continuousMapRingObjOfUniverse E).obj ⟶ (profiniteToProEtOf X).op ⋙ P)
    (σ : P ⟶ ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf X E)).obj)
    (hp : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (hσ : η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op σ =
      (comparisonAdjoint X E).hom) : IsIso (σ.app (Opposite.op U)) := by
  let T := pointLanComponents X U inferInstance wU
  let b (S : Profinite.{u}) : (U ⟶ (profiniteToProEtOf X).obj S) ≃ (T ⟶ S) :=
    (integralPointComponentsEquiv X U S).trans (profiniteHomContinuousEquiv T S).symm
  have hb (S S' : Profinite.{u}) (g : S ⟶ S') (f : U ⟶ (profiniteToProEtOf X).obj S) :
      b S' (f ≫ (profiniteToProEtOf X).map g) = b S f ≫ g := by
    apply ConcreteCategory.hom_injective
    exact integralPointComponentsEquiv_target X U S S' g f
  let q := (b T).symm (𝟙 T)
  let a := η.app (Opposite.op T) ≫ P.map q.op
  have hi' := (hp (Opposite.op U)).isIso_ι_app_of_isTerminal
    (CostructuredArrow.mk (S := (profiniteToProEtOf X).op) q.op)
    (kanTerminal (profiniteToProEtOf X) U T b hb)
  have hi : IsIso a := hi'
  let Q := ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf X E)).obj
  have h : a ≫ σ.app (Opposite.op U) =
      (comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op := by
    dsimp only [a]
    rw [Category.assoc, σ.naturality]
    exact congrArg (fun f ↦ f ≫ Q.map q.op)
      (congr_app hσ (Opposite.op T))
  have hq (x : U.left) : profiniteTestProjection X T (q.left x) = ConnectedComponents.mk x := by
    have h := congrArg (fun f : T ⟶ T ↦ f (ConnectedComponents.mk x))
      ((b T).apply_symm_apply (𝟙 T))
    change integralPointComponentsEquiv X U T q (ConnectedComponents.mk x) = _ at h
    rw [integralPointComponentsEquiv_apply] at h
    exact h
  have hbij : Function.Bijective
      ((comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op) := by
    constructor
    · intro f g he
      apply ULift.ext
      ext t
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
      have h := congrArg (fun f ↦ f.down x) he
      change f.down (profiniteTestProjection X T (q.left x)) =
        g.down (profiniteTestProjection X T (q.left x)) at h
      simpa only [hq] using h
    · intro f
      refine ⟨ULift.up ⟨f.down.continuous.connectedComponentsLift,
        f.down.continuous.connectedComponentsLift_continuous⟩, ?_⟩
      apply ULift.ext
      ext x
      change f.down.continuous.connectedComponentsLift
        (profiniteTestProjection X T (q.left x)) = f.down x
      rw [hq, Continuous.connectedComponentsLift_apply_coe]
  have : IsIso (a ≫ σ.app (Opposite.op U)) := by
    rw [h]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsIso.of_isIso_comp_left a _

private lemma comparison_basis_isIso (X : Scheme.{u}) (E : Type u)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (wU : PointLanWeaklyContractible X U) :
    IsIso ((comparison X E).hom.app (Opposite.op U)) := by
  let F := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let Λ := Profinite.continuousMapRingObjOfUniverse E
  let H := (sheafCompose K (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (continuousCoefficientRingSheaf X E)
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).IsContinuous
      (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  have : F.IsContinuous J K := by
    exact Functor.isContinuous_comp profiniteToProEt
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) J
      (Scheme.ProEt.topology specZ) K
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    AddCommGrpCat.{u + 1} J K
  let e := Adjunction.leftAdjointUniq a b
  let f := (b.homEquiv Λ H).symm (comparisonAdjoint X E)
  have hcomp : comparison X E = e.hom.app Λ ≫ f := by
    apply (a.homEquiv Λ H).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [comparison, Equiv.apply_symm_apply]
    change comparisonAdjoint X E = (b.homEquiv Λ H) f
    exact ((b.homEquiv Λ H).apply_symm_apply (comparisonAdjoint X E)).symm
  let P := F.op.lan.obj Λ.obj
  let η := F.op.lanUnit.app Λ.obj
  let hp := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension P η
  have hu := (proEtale_sheafification_wcontractible_sections X).2.1 Λ P η hp U
    inferInstance wU
  have : IsIso ((toSheafify K P).app (Opposite.op U)) := hu.1
  have hunit : (toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U) =
      (kanComparison X E).app (Opposite.op U) := by
    change (((sheafificationAdjunction K AddCommGrpCat.{u + 1}).homEquiv P H)
      f).app (Opposite.op U) = _
    simp only [ObjectProperty.ι_obj,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.restrictFullyFaithful, Functor.id_obj, Functor.comp_obj,
      Functor.whiskeringLeft_obj_obj, Functor.FullyFaithful.homEquiv,
      Functor.FullyFaithful.id, Iso.refl_symm, Equiv.trans_def, Adjunction.comp_homEquiv,
      Equiv.symm_mk, Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_trans,
      Iso.homCongr_symm, Equiv.trans_apply, Equiv.coe_fn_mk, ObjectProperty.ι_map,
      Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Iso.app_inv, NatTrans.id_app,
      Category.id_comp, Iso.symm_inv, Iso.app_hom, Iso.refl_hom, Category.comp_id,
      kanComparison, f, b]
    erw [Category.id_comp, Category.comp_id, Equiv.apply_symm_apply]
  have : IsIso ((kanComparison X E).app (Opposite.op U)) :=
    kanComparison_isIso X E U wU P η (kanComparison X E) hp (kanComparison_unit X E)
  have : IsIso (f.hom.app (Opposite.op U)) := by
    have : IsIso ((toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U)) := by
      rw [hunit]
      infer_instance
    exact IsIso.of_isIso_comp_left ((toSheafify K P).app (Opposite.op U)) _
  rw [hcomp]
  change IsIso ((e.hom.app Λ).hom.app (Opposite.op U) ≫ f.hom.app (Opposite.op U))
  infer_instance

/-- The canonical realization is an isomorphism for totally disconnected topological rings.
Source: HRS Example 3.1; the point-Lan affine evaluation proof.
(auxiliary; not a blueprint node) -/
theorem comparison_isIso (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    IsIso (comparison X T) :=
  isIso_of_affine_weaklyContractible X (comparison X T) (fun U hU wU ↦ by
    let _ := hU
    exact comparison_basis_isIso X T U wU)

end AlgebraicGeometry.ProEtale.ContinuousRingUniverse
