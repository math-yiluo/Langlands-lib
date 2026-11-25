/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Localization of the tensor-pullback unit on an open set

Source: Stacks Project, Tags 0096 and 01E8, local degree-zero projection formula.
(blueprint: lem-sc-tensor-unit-open-localization)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

noncomputable section
open CategoryTheory.Limits CategoryTheory.Functor Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits TopologicalSpace in
private local instance tensorPullbackOver_continuous
    {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Opens Y) :
    (Over.post (X := V) (Opens.map g.base)).IsContinuous
      ((Opens.grothendieckTopology Y).over V)
      ((Opens.grothendieckTopology X).over ((Opens.map g.base).obj V)) := by
  have : Limits.PreservesFiniteLimits (Opens.map g.base) :=
    preservesFiniteLimits_of_flat _
  have : RepresentablyFlat (Over.post (X := V) (Opens.map g.base)) :=
    flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_opens_map g.base).overPost V)

open CategoryTheory.Limits TopologicalSpace in
private local instance tensorPullbackOver_final
    {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Opens Y) :
    (Over.post (X := V) (Opens.map g.base)).Final := by
  have : Limits.PreservesFiniteLimits (Opens.map g.base) :=
    preservesFiniteLimits_of_flat _
  infer_instance

open CategoryTheory.Limits TopologicalSpace in
/-- The structure map restricted to the slice site over V. -/
private def tensorPullbackOverRingHom
    {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Opens Y) :
    (Y.ringCatSheaf).over V ⟶
      ((Over.post (X := V) (Opens.map g.base)).sheafPushforwardContinuous
        RingCat.{u} ((Opens.grothendieckTopology Y).over V)
        ((Opens.grothendieckTopology X).over ((Opens.map g.base).obj V))).obj
          ((X.ringCatSheaf).over ((Opens.map g.base).obj V)) :=
  ((Over.forget V).sheafPushforwardContinuous RingCat.{u}
    ((Opens.grothendieckTopology Y).over V) (Opens.grothendieckTopology Y)).map
      (show Y.ringCatSheaf ⟶
        ((Opens.map g.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
            (X.ringCatSheaf) from
        ⟨Functor.whiskerRight g.c (forget₂ CommRingCat RingCat)⟩)

-- The product comparison expresses g⁻¹(V ∩ W) = g⁻¹(V) ∩ g⁻¹(W).
open CategoryTheory.Limits TopologicalSpace in
private def tensorPullbackOverStarIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Opens Y) :
    Opens.map g.base ⋙ Over.star ((Opens.map g.base).obj V) ≅
      Over.star V ⋙ Over.post (Opens.map g.base) := by
  have : Limits.PreservesFiniteLimits (Opens.map g.base) :=
    preservesFiniteLimits_of_flat _
  refine NatIso.ofComponents (fun W ↦
    Over.isoMk (Limits.PreservesLimitPair.iso (Opens.map g.base) V W).symm ?_) ?_
  · apply Subsingleton.elim
  · intro W W' f
    ext
    apply Subsingleton.elim

-- Right adjoints to the two orders of restriction and pullback agree. The final
-- calculation checks the scalar maps, rather than only the underlying abelian sheaves.
open CategoryTheory.Limits TopologicalSpace in
private def tensorPullbackOverRightIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Opens Y) :
    SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) ((Opens.map g.base).obj V)) ⋙
        Modules.pushforward g ≅
      SheafOfModules.pushforward.{u} (tensorPullbackOverRingHom g V) ⋙
        SheafOfModules.pushforward.{u}
          (SheafOfModules.pushforwardOver (R := Y.ringCatSheaf) V) := by
  let F := Opens.map g.base
  let U := F.obj V
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology X
  let φ : Y.ringCatSheaf ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj
      (X.ringCatSheaf) := ⟨Functor.whiskerRight g.c (forget₂ CommRingCat RingCat)⟩
  let ψX := SheafOfModules.pushforwardOver (R := X.ringCatSheaf) U
  let ψY := SheafOfModules.pushforwardOver (R := Y.ringCatSheaf) V
  have : (F ⋙ Over.star U).IsContinuous J (K.over U) :=
    Functor.isContinuous_comp _ _ _ K _
  have : (Over.star V ⋙ Over.post F).IsContinuous J (K.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over V) _
  refine SheafOfModules.pushforwardComp φ ψX ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp ψY (tensorPullbackOverRingHom g V)).symm
  refine SheafOfModules.pushforwardCongr₂ _
    (tensorPullbackOverStarIso g V).symm ?_
  ext W r
  simp only [Iso.symm_hom, Category.assoc, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.whiskerRight_app, Functor.op_obj,
    Functor.comp_obj, NatTrans.op_app, Functor.sheafPushforwardContinuous_obj_obj_map,
    Over.forget_obj, Quiver.Hom.unop_op, Over.forget_map, RingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  change X.sheaf.obj.map (prodComparison (Opens.map g.base) V W.unop).op
    (X.sheaf.obj.map prod.snd.op (g.c.app W r)) =
      g.c.app (Opposite.op (V ⨯ W.unop)) (Y.sheaf.obj.map prod.snd.op r)
  rw [← Functor.map_comp_apply, ← op_comp, Limits.prodComparison_snd]
  exact (ConcreteCategory.congr_hom
    (g.c.naturality (Limits.prod.snd : V ⨯ W.unop ⟶ W.unop).op) r).symm


private def tensorPushforwardOverIso {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Opens Y) :
    Modules.pushforward g ⋙ SheafOfModules.overFunctor Y.ringCatSheaf V ≅
      SheafOfModules.overFunctor X.ringCatSheaf ((Opens.map g.base).obj V) ⋙
        SheafOfModules.pushforward.{u} (tensorPullbackOverRingHom g V) :=
  Iso.refl _

private theorem overAdjunction_counit_isIso {Y : Scheme.{u}} (U : Opens Y) :
    IsIso (SheafOfModules.overPushforwardOverAdj.{u} (R := Y.ringCatSheaf) U).counit := by
  have : ∀ N, IsIso
      ((SheafOfModules.overPushforwardOverAdj.{u} (R := Y.ringCatSheaf) U).counit.app N) := by
    intro N
    let F := SheafOfModules.toSheaf (Y.ringCatSheaf.over U) ⋙
      sheafToPresheaf ((Opens.grothendieckTopology Y).over U) AddCommGrpCat.{u}
    have : IsIso (F.map ((SheafOfModules.overPushforwardOverAdj U).counit.app N)) := by
      have : ∀ W, IsIso
          ((((SheafOfModules.toSheaf (Y.ringCatSheaf.over U)) ⋙
            sheafToPresheaf _ AddCommGrpCat.{u}).map
              ((SheafOfModules.overPushforwardOverAdj U).counit.app N)).app W) := by
        intro W
        let i : (Over.star U).obj W.unop.left ⟶ W.unop :=
          Over.homMk prod.snd (by apply Subsingleton.elim)
        have : IsIso ((Over.forgetAdjStar U).unit.app W.unop) :=
          ⟨⟨i, by ext; apply Subsingleton.elim, by ext; apply Subsingleton.elim⟩⟩
        change IsIso (N.val.presheaf.map ((Over.forgetAdjStar U).unit.app W.unop).op)
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ F
  exact NatIso.isIso_of_isIso_app _

private theorem localized_unit_of_invertible_comparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (R : C ⥤ D) (S : D ⥤ C) (a : R ⊣ S) (T : C ⥤ C) (η : 𝟭 C ⟶ T)
    [R.Additive] [S.Additive] [T.Additive] [IsIso a.counit]
    (h : ∀ M, IsIso (R.map (T.map (a.unit.app M)))) :
    ∃ (H : D ⥤ D) (α : 𝟭 D ⟶ H) (θ : R ⋙ H ≅ T ⋙ R),
      H.Additive ∧ ∀ M, R.map (η.app M) = α.app (R.obj M) ≫ θ.hom.app M := by
  let H := S ⋙ T ⋙ R
  let α : 𝟭 D ⟶ H :=
    inv a.counit ≫ whiskerRight (whiskerLeft S η) R
  let β : T ⋙ R ⟶ R ⋙ H := whiskerRight a.unit (T ⋙ R)
  have : ∀ M, IsIso (β.app M) := h
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨H, α, (asIso β).symm, inferInstance, ?_⟩
  intro M
  apply (cancel_mono (β.app M)).1
  simp only [Iso.symm_hom, asIso_inv, Category.assoc, NatIso.isIso_inv_app, IsIso.inv_hom_id,
    Category.comp_id]
  change R.map (η.app M) ≫ R.map (T.map (a.unit.app M)) =
    (inv a.counit).app (R.obj M) ≫ R.map (η.app (S.obj (R.obj M)))
  have hn := η.naturality (a.unit.app M)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [← R.map_comp, ← hn, R.map_comp]
  congr 1
  apply (cancel_mono (a.counit.app (R.obj M))).1
  simp [a.left_triangle_components M]

/-- The pullback-pushforward functor and its adjunction unit restrict to an
additive endofunctor and a natural transformation on the open slice site.
Source: Stacks Project, Tag 0096 (adjunction) and Tag 01E8 (local calculation).
(blueprint: lem-sc-tensor-unit-open-localization)

Proof: Let R be restriction to U and S its right adjoint, with unit ι and
counit ε. The counit is invertible: on the slice every W is already contained
in U, so the map W → U ∩ W is an isomorphism. Put P = tensorPullback p and
Q = pushforward p. On V = p⁻¹U construct the restricted ring map and its
pullback/pushforward adjunction PU ⊣ QU. Inverse image preserves intersections;
naturality of p.c identifies the scalar maps, giving SX ⋙ Q ≅ QU ⋙ S.
Uniqueness of left adjoints then gives R ⋙ PU ≅ P ⋙ RX. Direct-image restriction
also gives Q ⋙ R ≅ RX ⋙ QU, definitionally. The triangle identity makes R(ι_M)
invertible; transporting through these comparisons shows R(Q(P(ι_M))) is
invertible. Define H = S ⋙ P ⋙ Q ⋙ R, α_N = ε_N⁻¹ ; R(η_(S N)), and θ_M as
the inverse of R(Q(P(ι_M))). Naturality of η gives the required equation after
cancelling θ_M⁻¹, since R(ι_M) = ε_(R M)⁻¹ by the triangle identity. Sectionwise
pushforward and restriction are additive, and adjunction transfers additivity
to P. Thus H is additive. All constructions apply when U is empty -/
theorem tensorPullback_unit_open_localization {X Y : Scheme.{u}} (p : X ⟶ Y)
    (U : Opens Y) :
    ∃ (H : SheafOfModules.{u} (Y.ringCatSheaf.over U) ⥤
        SheafOfModules.{u} (Y.ringCatSheaf.over U))
      (α : 𝟭 _ ⟶ H)
      (θ : SheafOfModules.overFunctor Y.ringCatSheaf U ⋙ H ≅
        Modules.tensorPullback p ⋙ Modules.pushforward p ⋙
          SheafOfModules.overFunctor Y.ringCatSheaf U),
      H.Additive ∧ ∀ M : Y.Modules,
        ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app M).over U =
          α.app (M.over U) ≫ θ.hom.app M := by
  let R := SheafOfModules.overFunctor Y.ringCatSheaf U
  let S := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := Y.ringCatSheaf) U)
  let a : R ⊣ S := SheafOfModules.overPushforwardOverAdj U
  have : IsIso a.counit := overAdjunction_counit_isIso U
  have : R.Additive := ⟨by intros; ext W m; rfl⟩
  have : S.Additive := ⟨by intros; ext W m; rfl⟩
  let P := Modules.tensorPullback p
  let Q := Modules.pushforward p
  let adjP := Classical.choose (Modules.exists_tensorPullbackAdjunction p)
  have : P.Additive := adjP.left_adjoint_additive
  have : Q.Additive := adjP.right_adjoint_additive
  let V := (Opens.map p.base).obj U
  let RX := SheafOfModules.overFunctor X.ringCatSheaf V
  let aX := SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) V
  let PU := SheafOfModules.pullback.{u} (tensorPullbackOverRingHom p U)
  let QU := SheafOfModules.pushforward.{u} (tensorPullbackOverRingHom p U)
  let adjU := SheafOfModules.pullbackPushforwardAdjunction.{u} (tensorPullbackOverRingHom p U)
  let e : R ⋙ PU ≅ P ⋙ RX :=
    (a.comp adjU).leftAdjointUniq
      ((adjP.comp aX).ofNatIsoRight (tensorPullbackOverRightIso p U))
  apply localized_unit_of_invertible_comparison R S a (P ⋙ Q) adjP.unit
  intro M
  have : IsIso (R.map (a.unit.app M)) := by
    have h := a.left_triangle_components M
    exact IsIso.of_isIso_fac_right h
  have : IsIso ((R ⋙ PU).map (a.unit.app M)) :=
    PU.map_isIso (R.map (a.unit.app M))
  have : IsIso ((P ⋙ RX).map (a.unit.app M)) :=
    (NatIso.isIso_map_iff e (a.unit.app M)).1 inferInstance
  have : IsIso ((RX ⋙ QU).map (P.map (a.unit.app M))) :=
    QU.map_isIso ((P ⋙ RX).map (a.unit.app M))
  exact (NatIso.isIso_map_iff (tensorPushforwardOverIso p U)
    (P.map (a.unit.app M))).2 inferInstance

end
end AlgebraicGeometry.Scheme
