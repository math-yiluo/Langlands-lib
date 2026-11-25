/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Ringed localization for continuous cocontinuous restriction

Source: Stacks Project, Tag 04IE; sites.tex Tag 00XO
(blueprint: lem-weil-pbc-continuous-cocontinuous-ringed-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F J K] [Functor.IsCocontinuous F J K]
variable (R : Sheaf K RingCat.{u})

private abbrev restrictedRing := (F.sheafPushforwardContinuous RingCat J K).obj R

private abbrev familyAmbient (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) (V : Dᵒᵖ) :=
  ∀ (U : Cᵒᵖ) (ψ : V ⟶ F.op.obj U),
    (ModuleCat.restrictScalars (R.obj.map ψ).hom).obj (M.val.obj U)

private def familyModule (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) (V : Dᵒᵖ) :
    Submodule (R.obj.obj V) (familyAmbient F R M V) where
  carrier := {s | ∀ (U W : Cᵒᵖ) (a : U ⟶ W) (ψ : V ⟶ F.op.obj U),
    M.val.map a (s U ψ) = s W (ψ ≫ F.op.map a)}
  zero_mem' := by
    intro U W a ψ
    change M.val.map a 0 = 0
    exact map_zero _
  add_mem' := by
    intro s t hs ht U W a ψ
    change M.val.map a (s U ψ + t U ψ) = _
    rw [map_add, hs, ht]
    rfl
  smul_mem' := by
    intro r s hs U W a ψ
    change M.val.map a (R.obj.map ψ r • s U ψ) = _
    rw [M.val.map_smul, hs]
    change R.obj.map (F.op.map a) (R.obj.map ψ r) • _ = _
    rw [← R.obj.map_comp_apply]
    rfl

omit [Functor.IsCocontinuous F J K] in
private theorem family_smul_val
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) (V : Dᵒᵖ)
    (r : R.obj.obj V) (s : familyModule F R M V) (U : Cᵒᵖ) (ψ : V ⟶ F.op.obj U) :
    (r • s).val U ψ = R.obj.map ψ r • s.val U ψ := rfl

omit [Functor.IsCocontinuous F J K] in
private theorem family_add_val
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) (V : Dᵒᵖ)
    (s t : familyModule F R M V) (U : Cᵒᵖ) (ψ : V ⟶ F.op.obj U) :
    (s + t).val U ψ = s.val U ψ + t.val U ψ := rfl

omit [Functor.IsCocontinuous F J K] in
private theorem family_eval_linear
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) (U : Cᵒᵖ)
    (a : (restrictedRing (J := J) F R).obj.obj U)
    (x y : familyModule F R M (F.op.obj U)) :
    (a • x + y).val U (𝟙 _) =
      a • (show M.val.obj U from x.val U (𝟙 _)) +
        (show M.val.obj U from y.val U (𝟙 _)) := by
  erw [family_add_val, family_smul_val]
  rw [Functor.map_id_apply]

private noncomputable def familyPresheaf (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) :
    PresheafOfModules.{u} R.obj where
  obj V := ModuleCat.of _ (familyModule F R M V)
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of _ (familyModule F R M W)))
    { toFun s := ⟨fun U ψ ↦ s.val U (f ≫ ψ), by
        intro U U' a ψ
        exact (s.property U U' a (f ≫ ψ)).trans (by rw [Category.assoc])⟩
      map_add' := by intros; rfl
      map_smul' := by
        intro r s
        apply Subtype.ext
        funext U ψ
        change R.obj.map (f ≫ ψ) r • s.val U (f ≫ ψ) =
          R.obj.map ψ (R.obj.map f r) • s.val U (f ≫ ψ)
        rw [R.obj.map_comp_apply] }
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext U ψ
    change s.val U (𝟙 V ≫ ψ) = s.val U ψ
    rw [Category.id_comp]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext U ψ
    change s.val U ((f ≫ g) ≫ ψ) = s.val U (f ≫ (g ≫ ψ))
    rw [Category.assoc]

private def familyTypeEquiv (M : SheafOfModules.{u} (restrictedRing (J := J) F R))
    (V : D) :
    familyModule F R M (op V) ≃
      (F.op ⋙ yoneda.obj V ⟶ M.val.presheaf ⋙ forget AddCommGrpCat) where
  toFun s :=
    { app U := ↾fun ψ ↦ s.val U ψ.op
      naturality := by
        intro U W a
        ext ψ
        exact (s.property U W a ψ.op).symm }
  invFun α := ⟨fun U ψ ↦ α.app U ψ.unop, by
    intro U W a ψ
    exact (α.naturality_apply a ψ.unop).symm⟩
  left_inv s := rfl
  right_inv α := rfl

private noncomputable def familyRanEquiv
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) (V : D) :
    familyModule F R M (op V) ≃
      (F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat)).obj (op V) :=
  (familyTypeEquiv F R M V).trans
    (((F.op.ranAdjunction (Type u)).homEquiv (yoneda.obj V)
      (M.val.presheaf ⋙ forget AddCommGrpCat)).trans yonedaEquiv)

omit [Functor.IsCocontinuous F J K] in
private theorem familyRanEquiv_eval
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) (V : D)
    (s : familyModule F R M (op V)) (U : C) (ψ : F.obj U ⟶ V) :
    (F.op.ranCounit.app (M.val.presheaf ⋙ forget AddCommGrpCat)).app (op U)
      ((F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat)).map ψ.op
        (familyRanEquiv F R M V s)) = s.val (op U) ψ.op := by
  let adj := F.op.ranAdjunction (Type u)
  have h := adj.homEquiv (yoneda.obj V) (M.val.presheaf ⋙ forget AddCommGrpCat)
    |>.symm_apply_apply (familyTypeEquiv F R M V s)
  have he : adj.homEquiv (yoneda.obj V) (M.val.presheaf ⋙ forget AddCommGrpCat)
      (familyTypeEquiv F R M V s) = yonedaEquiv.symm (familyRanEquiv F R M V s) :=
    (yonedaEquiv.symm_apply_apply _).symm
  rw [he] at h
  rw [Adjunction.homEquiv_counit] at h
  change (Functor.whiskerLeft F.op (yonedaEquiv.symm (familyRanEquiv F R M V s))) ≫
    F.op.ranCounit.app (M.val.presheaf ⋙ forget AddCommGrpCat) = _ at h
  exact congrArg (fun k ↦ k.app (op U) ψ) h

private theorem ran_ext (P : Cᵒᵖ ⥤ Type u) (V : D)
    (x y : (F.op.ran.obj P).obj (op V))
    (h : ∀ (U : C) (ψ : F.obj U ⟶ V),
      (F.op.ranCounit.app P).app (op U) ((F.op.ran.obj P).map ψ.op x) =
        (F.op.ranCounit.app P).app (op U) ((F.op.ran.obj P).map ψ.op y)) : x = y := by
  apply yonedaEquiv.symm.injective
  apply ((F.op.ranAdjunction (Type u)).homEquiv (yoneda.obj V) P).symm.injective
  ext U ψ
  exact h U.unop ψ

private noncomputable def familyRanIso
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) :
    (familyPresheaf F R M).presheaf ⋙ forget AddCommGrpCat ≅
      F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat) :=
  NatIso.ofComponents (fun V ↦ (familyRanEquiv F R M V.unop).toIso) (by
    intro V W f
    ext s
    apply ran_ext F _ W.unop
    intro U ψ
    change (F.op.ranCounit.app (M.val.presheaf ⋙ forget AddCommGrpCat)).app (op U)
      ((F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat)).map ψ.op (familyRanEquiv F R M W.unop
        ((familyPresheaf F R M).map f s))) =
      (F.op.ranCounit.app (M.val.presheaf ⋙ forget AddCommGrpCat)).app (op U)
        ((F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat)).map ψ.op
          ((F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat)).map f
          (familyRanEquiv F R M V.unop s)))
    rw [familyRanEquiv_eval, ← Functor.map_comp_apply]
    exact (familyRanEquiv_eval F R M V.unop s U (ψ ≫ f.unop)).symm)

private theorem family_isSheaf
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R)) :
    Presheaf.IsSheaf K (familyPresheaf F R M).presheaf := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget K _ (forget AddCommGrpCat)).mpr
  apply (Presheaf.isSheaf_of_iso_iff (familyRanIso F R M)).mpr
  exact ran_isSheaf_of_isCocontinuous F K
    ((sheafCompose J (forget AddCommGrpCat)).obj ((SheafOfModules.toSheaf _).obj M))

private noncomputable def familyFunctor :
    SheafOfModules.{u} (restrictedRing (J := J) F R) ⥤ SheafOfModules.{u} R where
  obj M := ⟨familyPresheaf F R M, family_isSheaf F R M⟩
  map {M N} f := ⟨{
    app V := ModuleCat.ofHom
      { toFun s := ⟨fun U ψ ↦ f.val.app U (s.val U ψ), by
          intro U W a ψ
          rw [← PresheafOfModules.naturality_apply f.val, s.property]⟩
        map_add' := by
          intro s t
          apply Subtype.ext
          funext U ψ
          exact map_add _ _ _
        map_smul' := by
          intro r s
          apply Subtype.ext
          funext U ψ
          exact (f.val.app U).hom.map_smul (R.obj.map ψ r) (s.val U ψ) }
    naturality := by
      intro V W g
      ext s
      rfl }⟩
  map_id M := by ext V s; rfl
  map_comp f g := by ext V s; rfl

private noncomputable abbrev underlying {E : Type u} [SmallCategory E]
    {L : GrothendieckTopology E} (S : Sheaf L RingCat.{u}) :=
  SheafOfModules.toSheaf S ⋙ sheafCompose L (forget AddCommGrpCat)

private noncomputable def familyUnderlyingIso :
    familyFunctor F R ⋙ underlying R ≅
      underlying (restrictedRing (J := J) F R) ⋙
        F.sheafPushforwardCocontinuous (Type u) J K :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (familyRanIso F R M)) (by
    intro M N f
    ext V s
    apply ran_ext F _ V.unop
    intro U ψ
    change (F.op.ranCounit.app (N.val.presheaf ⋙ forget AddCommGrpCat)).app (op U)
      ((F.op.ran.obj (N.val.presheaf ⋙ forget AddCommGrpCat)).map ψ.op (familyRanEquiv F R N V.unop
        (((familyFunctor F R).map f).val.app V s))) = _
    rw [familyRanEquiv_eval]
    change f.val.app (op U) (s.val (op U) ψ.op) =
      (F.op.ranCounit.app (N.val.presheaf ⋙ forget AddCommGrpCat)).app (op U)
        ((F.op.ran.obj (N.val.presheaf ⋙ forget AddCommGrpCat)).map ψ.op
          ((F.op.ran.map ((underlying _).map f).hom).app V
            (familyRanEquiv F R M V.unop s)))
    erw [← (F.op.ran.map ((underlying _).map f).hom).naturality_apply ψ.op]
    have h := congrArg (fun k ↦ k ((F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat)).map ψ.op
      (familyRanEquiv F R M V.unop s)))
      (congr_app (F.op.ranCounit.naturality ((underlying _).map f).hom) (op U))
    change _ = f.val.app (op U)
      ((F.op.ranCounit.app (M.val.presheaf ⋙ forget AddCommGrpCat)).app (op U)
        ((F.op.ran.obj (M.val.presheaf ⋙ forget AddCommGrpCat)).map ψ.op
          (familyRanEquiv F R M V.unop s))) at h
    rw [familyRanEquiv_eval] at h
    exact h.symm)

private noncomputable def restrictionToFamily
    (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} (restrictedRing (J := J) F R))
    (f : (SheafOfModules.pushforward (F := F) (𝟙 (restrictedRing (J := J) F R))).obj M ⟶ N) :
    M ⟶ (familyFunctor F R).obj N := ⟨{
  app V := ModuleCat.ofHom
    { toFun m := ⟨fun U ψ ↦ f.val.app U (M.val.map ψ m), by
        intro U W a ψ
        dsimp only
        rw [← PresheafOfModules.naturality_apply]
        change f.val.app W (M.val.map (F.op.map a) (M.val.map ψ m)) = _
        rw [← M.val.map_comp_apply]⟩
      map_add' := by
        intro m n
        apply Subtype.ext
        funext U ψ
        change f.val.app U (M.val.map ψ (m + n)) = _
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro r m
        apply Subtype.ext
        funext U ψ
        change f.val.app U (M.val.map ψ (r • m)) =
          R.obj.map ψ r • f.val.app U (M.val.map ψ m)
        rw [M.val.map_smul, (f.val.app U).hom.map_smul] }
  naturality := by
    intro V W g
    ext m
    apply Subtype.ext
    funext U ψ
    change f.val.app U (M.val.map ψ (M.val.map g m)) =
      f.val.app U (M.val.map (g ≫ ψ) m)
    rw [M.val.map_comp_apply] }⟩

private noncomputable def familyToRestriction
    (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} (restrictedRing (J := J) F R))
    (f : M ⟶ (familyFunctor F R).obj N) :
    (SheafOfModules.pushforward (F := F) (𝟙 (restrictedRing (J := J) F R))).obj M ⟶ N := ⟨{
  app U := ModuleCat.ofHom
    { toFun m := (f.val.app (F.op.obj U) m).val U (𝟙 _)
      map_add' := by
        intro m n
        exact congrArg (fun s ↦ s.val U (𝟙 _)) ((f.val.app _).hom.map_add m n)
      map_smul' := by
        intro r m
        have h := congrArg (fun s ↦ s.val U (𝟙 _)) ((f.val.app _).hom.map_smul r m)
        dsimp only [familyFunctor, familyPresheaf] at h
        erw [family_smul_val] at h
        rw [Functor.map_id_apply] at h
        exact h }
  naturality := by
    intro U W a
    ext m
    change (f.val.app (F.op.obj W) (M.val.map (F.op.map a) m)).val W (𝟙 _) =
      N.val.map a ((f.val.app (F.op.obj U) m).val U (𝟙 _))
    rw [PresheafOfModules.naturality_apply]
    change (f.val.app (F.op.obj U) m).val W (F.op.map a ≫ 𝟙 _) = _
    rw [Category.comp_id, (f.val.app (F.op.obj U) m).property U W a (𝟙 _),
      Category.id_comp] }⟩

private noncomputable def familyHomEquiv
    (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} (restrictedRing (J := J) F R)) :
    ((SheafOfModules.pushforward (F := F) (𝟙 (restrictedRing (J := J) F R))).obj M ⟶ N) ≃
      (M ⟶ (familyFunctor F R).obj N) where
  toFun := restrictionToFamily F R M N
  invFun := familyToRestriction F R M N
  left_inv f := by
    ext U m
    change f.val.app U (M.val.map (𝟙 _) m) = f.val.app U m
    have h := congrArg (fun k ↦ k m) (M.val.map_id (F.op.obj U))
    exact congrArg (f.val.app U) h
  right_inv f := by
    ext V m
    apply Subtype.ext
    funext U ψ
    change (f.val.app (F.op.obj U) (M.val.map ψ m)).val U (𝟙 _) = (f.val.app V m).val U ψ
    rw [PresheafOfModules.naturality_apply]
    change (f.val.app V m).val U (ψ ≫ 𝟙 _) = _
    rw [Category.comp_id]

private noncomputable def familyAdjunction :
    SheafOfModules.pushforward (F := F) (𝟙 (restrictedRing (J := J) F R)) ⊣
      familyFunctor F R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := familyHomEquiv F R
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        ext U m
        rfl
      homEquiv_naturality_right := by
        intro M N N' f g
        ext V m
        apply Subtype.ext
        funext U ψ
        rfl }

private theorem familyTranspose_eval
    (M : SheafOfModules.{u} (restrictedRing (J := J) F R))
    (T : Sheaf K (Type u)) (z : T ⟶ (underlying R).obj ((familyFunctor F R).obj M))
    (U : Cᵒᵖ) (t : T.obj.obj (F.op.obj U)) :
    (((F.sheafAdjunctionCocontinuous (Type u) J K).homEquiv T _).symm
      (z ≫ (familyUnderlyingIso F R).hom.app M)).hom.app U t =
        (z.hom.app (F.op.obj U) t).val U (𝟙 _) := by
  rw [Adjunction.homEquiv_counit]
  change ((F.sheafAdjunctionCocontinuous (Type u) J K).counit.app
    ((underlying (restrictedRing (J := J) F R)).obj M)).hom.app U
    (familyRanEquiv F R M (F.obj U.unop) (z.hom.app (F.op.obj U) t)) = _
  rw [F.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  change (F.op.ranCounit.app (M.val.presheaf ⋙ forget AddCommGrpCat)).app U
    (familyRanEquiv F R M (F.obj U.unop) (z.hom.app (F.op.obj U) t)) = _
  exact (by simpa only [op_id, Functor.map_id_apply] using!
    familyRanEquiv_eval F R M (F.obj U.unop) (z.hom.app (F.op.obj U) t) U.unop (𝟙 _))

private noncomputable def ringedRestriction : RingedToposMorphism
    (restrictedRing (J := J) F R) R where
  inverse := F.sheafPushforwardContinuous (Type u) J K
  direct := F.sheafPushforwardCocontinuous (Type u) J K
  adj := F.sheafAdjunctionCocontinuous (Type u) J K
  leftExact := inferInstance
  ringMap := 𝟙 _
  ring_zero T z hz U t := hz (F.op.obj U) t
  ring_one T z hz U t := hz (F.op.obj U) t
  ring_add T x y z hz U t := hz (F.op.obj U) t
  ring_mul T x y z hz U t := hz (F.op.obj U) t
  modules := familyFunctor F R
  additive := ⟨by intro M N f g; ext V s; rfl⟩
  underlying := familyUnderlyingIso F R
  module_linear M T a x y z hz U t := by
    rw [familyTranspose_eval, familyTranspose_eval, familyTranspose_eval]
    change (z.hom.app (F.op.obj U) t).val U (𝟙 _) =
      (show (restrictedRing (J := J) F R).obj.obj U from a.hom.app (F.op.obj U) t) •
        (show M.val.obj U from (x.hom.app (F.op.obj U) t).val U (𝟙 _)) +
        (show M.val.obj U from (y.hom.app (F.op.obj U) t).val U (𝟙 _))
    have h := congrArg (fun s ↦ s.val U (𝟙 _)) (hz (F.op.obj U) t)
    exact h.trans (family_eval_linear F R M U (a.hom.app (F.op.obj U) t)
      (x.hom.app (F.op.obj U) t) (y.hom.app (F.op.obj U) t))

end

/-- Ringed localization for continuous cocontinuous restriction.

Source: literature/stacks-project/sites-modules.tex, Tag 04IE; sites.tex Tag 00XO
(blueprint: lem-weil-pbc-continuous-cocontinuous-ringed-restriction).
Proof: Use Mathlib Functor.sheafAdjunctionCocontinuous to obtain the set adjunction with continuous
precomposition as inverse image. Sectionwise limits prove left exactness. Take the structural
ring map to be the identity of the restricted ring. The generalized-element ring identities
follow by evaluating at F(U). Construct the module direct image by compatible families, defining
addition and the R-action coordinatewise; its underlying set sheaf is the same compatible-family
direct image. Transposition along the set adjunction takes linear maps to linear maps, since its
unit and counit are evaluated coordinatewise and the structural map is identity. Restrict its
hom equivalence to obtain the module adjunction. The same evaluation proves additivity, the
natural underlying comparison, and the module_linear field, using arbitrary rings rather than
commutative rings. -/
theorem continuous_cocontinuous_ringed_restriction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [Functor.IsContinuous F J K] [Functor.IsCocontinuous F J K]
    (R : Sheaf K RingCat.{u}) :
    ∃ f : RingedToposMorphism ((F.sheafPushforwardContinuous RingCat J K).obj R) R,
      f.inverse = F.sheafPushforwardContinuous (Type u) J K ∧
      (∀ (U : Cᵒᵖ)
        (x : (f.inverse.obj ((sheafCompose K (forget RingCat)).obj R)).obj.obj U),
        HEq (f.ringMap.hom.app U x) x) ∧
      Nonempty (SheafOfModules.pushforward (F := F)
        (𝟙 ((F.sheafPushforwardContinuous RingCat J K).obj R)) ⊣ f.modules) := by
  exact ⟨ringedRestriction (J := J) F R, rfl, fun U x ↦ HEq.rfl,
    ⟨familyAdjunction F R⟩⟩

end CategoryTheory
end
