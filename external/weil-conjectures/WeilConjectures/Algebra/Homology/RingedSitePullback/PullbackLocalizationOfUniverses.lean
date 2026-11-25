/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Localization of module pullback

Source: Stacks Project, Modules on Sites, Tag 04J0.
(blueprint: lem-pur-ringed-site-pullback-localization-universes)
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SheafOfModules.RingedSitePullback
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  {R : Sheaf J RingCat.{max u v w}} {S : Sheaf K RingCat.{max u v w}}
  (a : R ⟶ (U.sheafPushforwardContinuous RingCat J K).obj S)
  [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]

noncomputable def locMap (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))] :
    R.over V ⟶ ((Over.post (X := V) U).sheafPushforwardContinuous RingCat
      (J.over V) (K.over (U.obj V))).obj (S.over (U.obj V)) :=
  ⟨{ app T := a.hom.app (op T.unop.left)
     naturality _ _ f := a.hom.naturality ((Over.forget V).op.map f) }⟩

noncomputable def starPostIso (V : C) :
    Over.star V ⋙ Over.post U ≅ U ⋙ Over.star (U.obj V) :=
  NatIso.ofComponents
    (fun X ↦ Over.isoMk (asIso (prodComparison U V X)) (by
      dsimp
      simp)) (by
      intro X Y f
      ext
      dsimp
      change U.map (prod.map (𝟙 V) f) ≫ prodComparison U V Y =
        prodComparison U V X ≫ prod.map (𝟙 (U.obj V)) (U.map f)
      simpa only [U.map_id] using prodComparison_natural U (𝟙 V) f)

@[irreducible]
noncomputable def localRightIso (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))] :
    pushforward.{max u v w} (locMap a V) ⋙ pushforward (pushforwardOver (R := R) V) ≅
      pushforward (pushforwardOver (R := S) (U.obj V)) ⋙ pushforward a := by
  letI := Functor.isContinuous_comp (Over.star V) (Over.post U) J (J.over V)
    (K.over (U.obj V))
  letI := Functor.isContinuous_comp U (Over.star (U.obj V)) J K (K.over (U.obj V))
  refine pushforwardComp _ _ ≪≫ ?_ ≪≫ (pushforwardComp _ _).symm
  apply pushforwardCongr₂ (e := (starPostIso (U := U) V).symm)
  ext X r
  dsimp [locMap, pushforwardOver, starPostIso]
  change S.obj.map (inv (prodComparison U V X.unop)).op
      (a.hom.app (op (V ⨯ X.unop)) (R.obj.map prod.snd.op r)) =
    S.obj.map prod.snd.op (a.hom.app X r)
  have h := ConcreteCategory.congr_hom
    (a.hom.naturality (prod.snd : V ⨯ X.unop ⟶ X.unop).op) r
  change a.hom.app (op (V ⨯ X.unop)) (R.obj.map prod.snd.op r) =
    S.obj.map (U.map prod.snd).op (a.hom.app X r) at h
  rw [h]
  change (S.obj.map (U.map prod.snd).op ≫
    S.obj.map (inv (prodComparison U V X.unop)).op) (a.hom.app X r) = _
  rw [← S.obj.map_comp, ← op_comp]
  congr 3
  exact congrArg Quiver.Hom.op (by
    apply (cancel_epi (prodComparison U V X.unop)).1
    simp)

lemma local_overAdj_unit (V : C) (L : SheafOfModules.{max u v w} R)
    (X : Cᵒᵖ) (x : L.val.obj X) :
    ((overPushforwardOverAdj (R := R) V).unit.app L).val.app X x =
      L.val.map prod.snd.op x := by
  change L.val.map ((Over.forgetAdjStar V).counit.app X.unop).op x = _
  rw [Over.forgetAdjStar_counit_app]
  rfl

lemma local_right_inv (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    (N : SheafOfModules.{max u v w} (S.over (U.obj V)))
    (X : Cᵒᵖ) (x : N.val.obj (op ((Over.star (U.obj V)).obj (U.obj X.unop)))) :
    ((localRightIso a V).inv.app N).val.app X x =
      N.val.map ((Over.homMk (prodComparison U V X.unop) (by simp) :
        (Over.post U).obj ((Over.star V).obj X.unop) ⟶
          (Over.star (U.obj V)).obj (U.obj X.unop))).op x := by
  simp only [localRightIso, Iso.trans_inv, NatTrans.comp_app, comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    pushforwardComp_inv_app_val_app,
    pushforwardCongr₂, pushforwardNatIso_inv, pushforwardCongr_hom_app_val_app,
    pushforwardNatTrans_app_val_app_apply]
  rfl

@[irreducible]
noncomputable def localLeftIso (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint] :
    overFunctor R V ⋙ pullback (locMap a V) ≅
      pullback a ⋙ overFunctor S (U.obj V) :=
  Adjunction.leftAdjointUniq
    ((overPushforwardOverAdj (R := R) V).comp
      (pullbackPushforwardAdjunction (locMap a V)))
    (((pullbackPushforwardAdjunction a).comp
      (overPushforwardOverAdj (R := S) (U.obj V))).ofNatIsoRight
        (localRightIso a V).symm)

noncomputable def localComparison (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R) :
    (pullback (locMap a V)).obj (L.over V) ⟶ ((pullback a).obj L).over (U.obj V) :=
  ((pullbackPushforwardAdjunction (locMap a V)).homEquiv _ _).symm
    (((pullbackPushforwardAdjunction a).unit.app L).over V)

omit [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U] in
lemma localComparison_unit (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R) :
    (pullbackPushforwardAdjunction (locMap a V)).unit.app (L.over V) ≫
      (pushforward (locMap a V)).map (localComparison a V L) =
        ((pullbackPushforwardAdjunction a).unit.app L).over V :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

omit [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U] in
lemma localComparison_unit_apply (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R) (T : Over V) (m : L.val.obj (op T.left)) :
    (localComparison a V L).val.app (op ((Over.post U).obj T))
      (((pullbackPushforwardAdjunction (locMap a V)).unit.app (L.over V)).val.app
        (op T) m) =
      ((pullbackPushforwardAdjunction a).unit.app L).val.app (op T.left) m :=
  congrArg (fun f ↦ f.val.app (op T) m) (localComparison_unit a V L)

omit [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U] in
lemma local_push_map_apply {A B : SheafOfModules.{max u v w} S}
    (f : A ⟶ B) (X : Cᵒᵖ) (x : A.val.obj (op (U.obj X.unop))) :
    (((pushforward a).map f).val.app X).hom x =
      (f.val.app (op (U.obj X.unop))).hom x := rfl

lemma local_over_push_map_apply (V : C) {A B : SheafOfModules.{max u v w} R}
    (f : A ⟶ B) (X : Cᵒᵖ) (x : A.val.obj (op (V ⨯ X.unop))) :
    (((pushforward (pushforwardOver (R := R) V)).map (f.over V)).val.app X).hom x =
      (f.val.app (op (V ⨯ X.unop))).hom x := rfl

omit [HasFiniteLimits D] in
lemma local_over_val_map_apply (M : SheafOfModules.{max u v w} S) (V : D)
    {T T' : Over V} (f : T ⟶ T') (x : M.val.obj (op T'.left)) :
    ((M.over V).val.map f.op).hom x = (M.val.map f.left.op).hom x := rfl

-- Elaborate the comparison of composite adjunctions and their component units.
/-- The canonical localization comparison agrees with the isomorphism of left adjoints.
Source: Stacks Project, Modules on Sites, Tag 04J0.
(blueprint: lem-pur-ringed-site-pullback-localization-universes).

Proof: The right adjoints are identified using the product comparison
U(V × X) ≅ U(V) × U(X). Uniqueness of left adjoints gives an isomorphism.
Under the composite adjunctions, its mate is the restricted global unit:
naturality along the second projection and the product comparison equation
identify their components. Hence it is the canonical localization map. -/
lemma localComparison_eq (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R) :
    localComparison a V L = (localLeftIso a V).hom.app L := by
  let adj₁ := (overPushforwardOverAdj (R := R) V).comp
    (pullbackPushforwardAdjunction (locMap a V))
  let adj₂ := ((pullbackPushforwardAdjunction a).comp
    (overPushforwardOverAdj (R := S) (U.obj V))).ofNatIsoRight
      (localRightIso a V).symm
  unfold localLeftIso
  apply (adj₁.homEquiv _ _).injective
  change adj₁.homEquiv _ _ (localComparison a V L) =
    adj₁.homEquiv _ _ ((adj₁.leftAdjointUniq adj₂).hom.app L)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (overPushforwardOverAdj (R := R) V).homEquiv _ _
    ((pullbackPushforwardAdjunction (locMap a V)).homEquiv _ _
      (localComparison a V L)) = _
  erw [localComparison, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  change _ = (((pullbackPushforwardAdjunction a).comp
    (overPushforwardOverAdj (R := S) (U.obj V))).unit.app L) ≫
      (localRightIso a V).inv.app (((pullback a).obj L).over (U.obj V))
  have hcomp := Adjunction.comp_unit_app (pullbackPushforwardAdjunction a)
    (overPushforwardOverAdj (R := S) (U.obj V)) L
  rw [hcomp]
  ext X x
  change ((((pushforward (pushforwardOver V)).map
    (((pullbackPushforwardAdjunction a).unit.app L).over V)).val.app X).hom)
      ((((overPushforwardOverAdj (R := R) V).unit.app L).val.app X).hom x) =
    (((localRightIso a V).inv.app (((pullback a).obj L).over (U.obj V))).val.app X).hom
      ((((pushforward a).map
        ((overPushforwardOverAdj (R := S) (U.obj V)).unit.app
          ((pullback a).obj L))).val.app X).hom
        ((((pullbackPushforwardAdjunction a).unit.app L).val.app X).hom x))
  rw [local_overAdj_unit, local_right_inv]
  rw [local_over_push_map_apply, local_push_map_apply, local_overAdj_unit,
    local_over_val_map_apply]
  change ((pullbackPushforwardAdjunction a).unit.app L).val.app
    (op (V ⨯ X.unop)) (L.val.map prod.snd.op x) =
    ((pullback a).obj L).val.map (prodComparison U V X.unop).op
      (((pullback a).obj L).val.map prod.snd.op
        (((pullbackPushforwardAdjunction a).unit.app L).val.app X x))
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, prodComparison_snd]
  exact PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction a).unit.app L).val prod.snd.op x

instance localComparison_isIso (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R) : IsIso (localComparison a V L) := by
  rw [localComparison_eq]
  infer_instance

@[irreducible]
noncomputable def localHomEquiv (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R)
    (N : SheafOfModules.{max u v w} (S.over (U.obj V))) :
    (((pullback a).obj L).over (U.obj V) ⟶ N) ≃
      (L.over V ⟶ (pushforward (locMap a V)).obj N) :=
  (Iso.homCongr (asIso (localComparison a V L)) (Iso.refl N)).symm.trans
    ((pullbackPushforwardAdjunction (locMap a V)).homEquiv _ _)

lemma localHomEquiv_apply (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R)
    (N : SheafOfModules.{max u v w} (S.over (U.obj V)))
    (f : ((pullback a).obj L).over (U.obj V) ⟶ N) :
    localHomEquiv a V L N f =
      ((pullbackPushforwardAdjunction a).unit.app L).over V ≫
        (pushforward (locMap a V)).map f := by
  unfold localHomEquiv
  change (pullbackPushforwardAdjunction (locMap a V)).homEquiv _ _
    (localComparison a V L ≫ f) = _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    localComparison_unit]

lemma local_hom_ext (V : C)
    [(Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
    [(pushforward.{max u v w} a).IsRightAdjoint]
    [(pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
    (L : SheafOfModules.{max u v w} R)
    (N : SheafOfModules.{max u v w} (S.over (U.obj V)))
    (f g : ((pullback a).obj L).over (U.obj V) ⟶ N)
    (h : ∀ (T : Over V) (m : L.val.obj (op T.left)),
      f.val.app (op ((Over.post U).obj T))
          (((pullbackPushforwardAdjunction a).unit.app L).val.app (op T.left) m) =
        g.val.app (op ((Over.post U).obj T))
          (((pullbackPushforwardAdjunction a).unit.app L).val.app (op T.left) m)) :
    f = g := by
  apply (localHomEquiv a V L N).injective
  rw [localHomEquiv_apply, localHomEquiv_apply]
  ext T m
  exact h T.unop m

omit [U.IsContinuous J K] [HasFiniteLimits D] in
lemma local_continuous (hcover : CoverPreserving J K U) (V : C) :
    (Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V)) := by
  have := CategoryTheory.flat_of_preservesFiniteLimits (Over.post (X := V) U)
  exact (Functor.isContinuous_iff_coverPreserving (F := Over.post (X := V) U)).2
    (hcover.overPost V)

end SheafOfModules.RingedSitePullback
