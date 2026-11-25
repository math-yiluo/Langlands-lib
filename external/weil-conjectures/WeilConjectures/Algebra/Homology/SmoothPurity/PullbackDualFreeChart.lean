/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Finite-free chart calculation for the pulled dual

Source: Stacks Project, Modules on Sites, Tags 03EL, 03EO and 0GMX.
(blueprint: lem-pur-ringed-site-pullback-dual-free-chart)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

private theorem comparison_biproduct {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [HasFiniteBiproducts A] [HasFiniteBiproducts B]
    (F G : Aᵒᵖ ⥤ B) [F.Additive] [G.Additive] (α : F ⟶ G)
    (E : A) [IsIso (α.app (op E))] (I : Type*) [Finite I] :
    IsIso (α.app (op (⨁ fun _ : I ↦ E))) := by
  classical
  let := Fintype.ofFinite I
  let K := (Discrete.functor fun _ : I ↦ E).op
  have : IsIso (Functor.whiskerLeft K α) := by
    let (i : (Discrete I)ᵒᵖ) : IsIso ((Functor.whiskerLeft K α).app i) :=
      inferInstanceAs (IsIso (α.app (op E)))
    exact NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K α _ (biproduct.isLimit _).op

set_option autoImplicit false

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (N : PresheafOfModules.{max u v w} (R ⋙ forget₂ _ _))

/-- A section `n` of `N` over `U` gives the morphism `R|_U ⟶ N|_U`, `r ↦ r • n`. -/
private noncomputable def chart_homObjUnitInvApp {U : C} (n : N.obj (op U)) :
    (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj N :=
  (unitHomEquiv ((restrictOver R U).obj N)).symm
    (sectionsMk (fun W ↦ N.map W.unop.hom.op n) fun {W W'} f ↦ by
      change N.map f.unop.left.op (N.map W.unop.hom.op n) = N.map W'.unop.hom.op n
      rw [← map_comp_apply, ← op_comp, Over.w])

private lemma chart_map_id_apply' {X : Cᵒᵖ} (x : N.obj X) : N.map (𝟙 X) x = x := by
  rw [map_id]
  rfl

private lemma chart_homObjUnitInvApp_app_one {U : C} (n : N.obj (op U)) :
    (chart_homObjUnitInvApp N n).app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)) = n :=
  (congrArg (fun s ↦ s.val (op (Over.mk (𝟙 U))))
    ((unitHomEquiv ((restrictOver R U).obj N)).apply_symm_apply _)).trans
      ((N.congr_map_apply op_id n).trans (N.chart_map_id_apply' n))

/-- The sections of `homObj R N` over `X` are the sections of `N` over `X`. -/
private noncomputable def chart_homObjUnitIsoApp (X : Cᵒᵖ) : (homObj (unit _) N).obj X ≅ N.obj X :=
    { hom := ConcreteCategory.ofHom
        { toFun φ := φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))
          map_add' _ _ := rfl
          map_smul' r φ := by
            refine (restrictOver_smul_app_apply r φ _ _).trans ?_
            change R.map (𝟙 _) r • _ = _
            rw [R.map_id]
            rfl }
      inv := ConcreteCategory.ofHom
        { toFun n := chart_homObjUnitInvApp N n
          map_add' n n' := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op (n + n')) =
                (1 : R.obj (op W.unop.left)) •
                    (show N.obj (op W.unop.left) from N.map W.unop.hom.op n) +
                  (1 : R.obj (op W.unop.left)) •
                    (show N.obj (op W.unop.left) from N.map W.unop.hom.op n')
              rw [map_add, smul_add]
          map_smul' r n := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op (r • n)) =
                R.map W.unop.hom.op r • (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n)
              rw [one_smul, one_smul, N.map_smul]
              rfl }
      hom_inv_id := by
        ext φ : 2
        refine hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
          (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (1 : R.obj (op W.unop.left)) • (show N.obj (op W.unop.left) from
          N.map W.unop.hom.op (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop)))) =
            φ.app W (1 : R.obj (op W.unop.left))
        rw [one_smul]
        refine (naturality_apply φ
          (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj (op X.unop))).symm.trans ?_
        exact congrArg (φ.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op)
      inv_hom_id := by
        ext n
        exact chart_homObjUnitInvApp_app_one N n }

/-- **The internal hom out of the unit.** `homObj R N ≅ N`: a morphism `R|_U ⟶ N|_U` is
determined by the image of `1`. -/
private noncomputable def chart_homObjUnitIso : homObj (unit _) N ≅ N :=
  isoMk (chart_homObjUnitIsoApp N) fun X Y g ↦ by
    ext φ
    change φ.app (op (Over.mk (𝟙 Y.unop ≫ g.unop))) (1 : R.obj Y) =
      N.map g (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X))
    refine (restrictOver_hom_app_congr (M := unit _) (N := N) φ (Category.id_comp g.unop)
      (1 : R.obj Y)).trans (Eq.trans ?_ (naturality_apply φ
        (Over.homMk g.unop (Category.comp_id _) : Over.mk g.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj X)))
    exact congrArg (φ.app _) (unit_map_one (R := R ⋙ forget₂ _ _) g).symm

end PresheafOfModules

namespace SheafOfModules

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

section UnitHelpers

private noncomputable def chart_overValIso
    (M : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (V : C) :
    (M.over V).val ≅ (PresheafOfModules.restrictOver R.obj V).obj M.val :=
  PresheafOfModules.isoMk (fun T ↦
    (LinearEquiv.refl (R.obj.obj (op T.unop.left))
      (M.val.obj (op T.unop.left))).toModuleIso) fun _ _ _ ↦ rfl

private noncomputable def chart_unitHom
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : homObj (R := R) (unit _) N ⟶ N :=
  { val := { app := fun X ↦ (PresheafOfModules.chart_homObjUnitIsoApp.{u, v, w}
      (R := R.obj) N.val X).hom
             naturality := (PresheafOfModules.chart_homObjUnitIso.{u, v, w}
               (R := R.obj) N.val).hom.naturality } }

private noncomputable def chart_unitInv
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : N ⟶ homObj (R := R) (unit _) N :=
  { val := { app := fun X ↦ (PresheafOfModules.chart_homObjUnitIsoApp.{u, v, w}
      (R := R.obj) N.val X).inv
             naturality := (PresheafOfModules.chart_homObjUnitIso.{u, v, w}
               (R := R.obj) N.val).inv.naturality } }

@[irreducible]
private noncomputable def chart_unitHomIso
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : homObj (R := R) (unit _) N ≅ N :=
  { hom := chart_unitHom.{u, v, w} (R := R) N
    inv := chart_unitInv.{u, v, w} (R := R) N
    hom_inv_id := by
      apply hom_ext
      exact (PresheafOfModules.chart_homObjUnitIso.{u, v, w} (R := R.obj) N.val).hom_inv_id
    inv_hom_id := by
      apply hom_ext
      exact (PresheafOfModules.chart_homObjUnitIso.{u, v, w} (R := R.obj) N.val).inv_hom_id }

private lemma chart_unitHomIso_hom_eval
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (φ : (homObj (R := R) (unit _) N).val.obj (op V)) :
    (chart_unitHomIso.{u, v, w} (R := R) N).hom.val.app (op V) φ =
      φ.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V)) := by
  unfold chart_unitHomIso
  rfl

private lemma chart_unitHomIso_inv_eval
    (N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (n : N.val.obj (op V)) (m : R.obj.obj (op V)) :
    (((chart_unitHomIso.{u, v, w} (R := R) N).inv.val.app (op V) n).app
      (op (Over.mk (𝟙 V)))) m = m • n := by
  have h (T : Over V) (r : R.obj.obj (op T.left)) :
      (((chart_unitHomIso.{u, v, w} (R := R) N).inv.val.app (op V) n).app (op T)) r =
        r • (show N.val.obj (op T.left) from N.val.map T.hom.op n) := by
    unfold chart_unitHomIso
    rfl
  exact (h (Over.mk (𝟙 V)) m).trans
    (congrArg (m • ·) ((N.val.congr_map_apply op_id n).trans
      (PresheafOfModules.chart_map_id_apply' N.val n)))

@[irreducible]
private noncomputable def chart_overHomIso
    (M N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (V : C) :
    (homObj (R := R) M N).over V ≅ homObj (R := R.over V) (M.over V) (N.over V) :=
  (fullyFaithfulForget _).preimageIso <|
    chart_overValIso.{u, v, w} (R := R) (homObj (R := R) M N) V ≪≫
    PresheafOfModules.restrictOverHomObjIso (R := R.obj) M.val N.val V ≪≫
    ((PresheafOfModules.homFunctor ((Over.forget V).op ⋙ R.obj)).flip.obj
      ((PresheafOfModules.restrictOver R.obj V).obj N.val)).mapIso
        (chart_overValIso.{u, v, w} (R := R) M V).op ≪≫
    ((PresheafOfModules.homFunctor ((Over.forget V).op ⋙ R.obj)).obj
      (op (M.over V).val)).mapIso (chart_overValIso.{u, v, w} (R := R) N V).symm

private lemma chart_overHomIso_hom_eval
    (M N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (T : Over V) (φ : (homObj (R := R) M N).val.obj (op T.left))
    (W : Over T) (m : M.val.obj (op W.left.left)) :
    (((chart_overHomIso.{u, v, w} (R := R) M N V).hom.val.app (op T) φ).app (op W)) m =
      φ.app (op (Over.mk W.hom.left)) m := by
  unfold chart_overHomIso
  rfl

private lemma chart_overHomIso_inv_eval
    (M N : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (T : Over V)
    (φ : (homObj (R := R.over V) (M.over V) (N.over V)).val.obj (op T))
    (m : M.val.obj (op T.left)) :
    (((chart_overHomIso.{u, v, w} (R := R) M N V).inv.val.app (op T) φ).app
      (op (Over.mk (𝟙 T.left)))) m =
        φ.app (op (Over.mk (𝟙 T))) m := by
  have h := congrArg (fun f ↦ ((f.val.app (op T) φ).app
    (op (Over.mk (𝟙 T)))) m)
      (chart_overHomIso.{u, v, w} (R := R) M N V).inv_hom_id
  change (((chart_overHomIso.{u, v, w} (R := R) M N V).hom.val.app (op T)
    ((chart_overHomIso.{u, v, w} (R := R) M N V).inv.val.app (op T) φ)).app
      (op (Over.mk (𝟙 T)))) m = _ at h
  rw [chart_overHomIso_hom_eval] at h
  exact h

end UnitHelpers

set_option backward.isDefEq.respectTransparency true

section GlobalComparison

open SheafOfModules.RingedSitePullback
variable [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
  [(pushforward.{max u v w} a).IsRightAdjoint]
  (hcover : CoverPreserving J K U)
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

@[irreducible]
private noncomputable def dualComparison
    (L : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (pullback a).obj (homObj (R := R) L (unit _)) ⟶ homObj (R := S) ((pullback a).obj L) (unit _) :=
  (exists_pullback_pairing_transfer.{u, v, w} (R := R) (S := S) a hcover
    inferInstance L (homObj (R := R) L (unit _)) (𝟙 _)).choose

private lemma dualComparison_spec
    (L : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (φ : (homObj (R := R) L (unit _)).val.obj (op V)) (m : L.val.obj (op V)) :
    (((dualComparison.{u, v, w} (R := R) (S := S) a hcover L).val.app (op (U.obj V))
      (((pullbackPushforwardAdjunction a).unit.app (homObj (R := R) L (unit _))).val.app
        (op V) φ)).app (op (Over.mk (𝟙 (U.obj V)))))
      (((pullbackPushforwardAdjunction a).unit.app L).val.app (op V) m) =
        a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) m) := by
  unfold dualComparison
  exact (exists_pullback_pairing_transfer.{u, v, w} (R := R) (S := S) a hcover
    inferInstance L (homObj (R := R) L (unit _)) (𝟙 _)).choose_spec.1 V φ m

private lemma dualComparison_unique
    (L : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (d : (pullback a).obj (homObj (R := R) L (unit _)) ⟶ homObj (R := S) ((pullback a).obj L)
      (unit _))
    (hd : ∀ (V : C) (φ : (homObj (R := R) L (unit _)).val.obj (op V)) (m : L.val.obj (op V)),
      ((d.val.app (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app (homObj (R := R) L (unit _))).val.app
          (op V) φ)).app (op (Over.mk (𝟙 (U.obj V)))))
        (((pullbackPushforwardAdjunction a).unit.app L).val.app (op V) m) =
          a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) m)) :
    d = dualComparison.{u, v, w} (R := R) (S := S) a hcover L := by
  unfold dualComparison
  exact (exists_pullback_pairing_transfer.{u, v, w} (R := R) (S := S) a hcover
    inferInstance L (homObj (R := R) L (unit _)) (𝟙 _)).choose_spec.2 d hd

private noncomputable abbrev chart_section
    (M : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (V : C)
    (m : M.val.obj (op V)) :=
  ((pullbackPushforwardAdjunction a).unit.app M).val.app (op V) m

private lemma dualComparison_natural
    (L M : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (b : L ⟶ M) :
    (pullback a).map (homObjMap (R := R) b (𝟙 (unit _))) ≫ dualComparison.{u, v, w} (R := R) (S
      := S) a hcover L =
      dualComparison.{u, v, w} (R := R) (S := S) a hcover M ≫ homObjMap (R := S) ((pullback
        a).map b) (𝟙 (unit _)) := by
  obtain ⟨d, hd, unique⟩ := exists_pullback_pairing_transfer.{u, v, w} (R := R) (S := S) a hcover
    inferInstance L (homObj (R := R) M (unit _)) (homObjMap (R := R) b (𝟙 _))
  apply (unique _ ?_).trans (unique _ ?_).symm
  · intro V φ m
    have hnat := (pullbackPushforwardAdjunction a).unit.naturality
      (homObjMap (R := R) b (𝟙 (unit _)))
    have heq : chart_section.{u, v, w} (R := R) (S := S) a (homObj (R := R) L (unit _)) V
        ((homObjMap (R := R) b (𝟙 (unit _))).val.app (op V) φ) =
        (((pullback a).map (homObjMap (R := R) b (𝟙 (unit _)))).val.app (op (U.obj V)))
          (chart_section.{u, v, w} (R := R) (S := S) a (homObj (R := R) M (unit _)) V φ) :=
      congrArg (fun f ↦ f.val.app (op V) φ) hnat
    exact (congrArg (fun ψ ↦ (((dualComparison.{u, v, w} (R := R) (S := S) a hcover L).val.app
      (op (U.obj V)) ψ).app
      (op (Over.mk (𝟙 (U.obj V)))))
        (chart_section.{u, v, w} (R := R) (S := S) a L V m)) heq).symm.trans
          (dualComparison_spec.{u, v, w} (R := R) (S := S) a hcover L V ((homObjMap (R := R) b
            (𝟙 (unit _))).val.app (op V) φ) m)
  · intro V φ m
    have hnat := (pullbackPushforwardAdjunction a).unit.naturality b
    have heq : chart_section.{u, v, w} (R := R) (S := S) a M V (b.val.app (op V) m) =
        (((pullback a).map b).val.app (op (U.obj V)))
          (chart_section.{u, v, w} (R := R) (S := S) a L V m) :=
      congrArg (fun f ↦ f.val.app (op V) m) hnat
    exact (congrArg (fun x ↦ (((dualComparison.{u, v, w} (R := R) (S := S) a hcover M).val.app
      (op (U.obj V))
      (chart_section.{u, v, w} (R := R) (S := S) a (homObj (R := R) M (unit _)) V φ)).app
        (op (Over.mk (𝟙 (U.obj V))))) x) heq).symm.trans
          (dualComparison_spec.{u, v, w} (R := R) (S := S) a hcover M V φ (b.val.app (op V) m))

set_option backward.isDefEq.respectTransparency false in
private lemma dualComparison_unit_isIso :
    IsIso (dualComparison.{u, v, w} (R := R) (S := S) a hcover (unit _)) := by
  let e := asIso (pullbackObjUnitToUnit a)
  let h := chart_unitHomIso (R := R) (unit _)
  let k := chart_unitHomIso (R := S) (unit _)
  let f := (pullback a).map h.hom ≫ e.hom ≫ k.inv ≫ homObjMap (R := S) e.hom (𝟙 (unit _))
  have hf : f = dualComparison.{u, v, w} (R := R) (S := S) a hcover (unit _) := by
    apply dualComparison_unique.{u, v, w} (R := R) (S := S) a hcover (unit _)
    intro V φ m
    have he (r : R.obj.obj (op V)) :
        e.hom.val.app (op (U.obj V))
            (((pullbackPushforwardAdjunction a).unit.app (unit _)).val.app (op V) r) =
          a.hom.app (op V) r := by
      have hh := pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit a
      rw [Adjunction.homEquiv_unit] at hh
      exact congrArg (fun g ↦ g.val.app (op V) r) hh
    have hn := congrArg (fun g ↦ g.val.app (op V) φ)
      ((pullbackPushforwardAdjunction a).unit.naturality h.hom)
    change ((pullbackPushforwardAdjunction a).unit.app (unit _)).val.app (op V)
        (h.hom.val.app (op V) φ) =
      ((pullback a).map h.hom).val.app (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app (homObj (R := R) (unit _) (unit _))).val.app
          (op V) φ) at hn
    change (((k.inv.val.app (op (U.obj V))
      (e.hom.val.app (op (U.obj V))
        (((pullback a).map h.hom).val.app (op (U.obj V))
          (((pullbackPushforwardAdjunction a).unit.app
            (homObj (R := R) (unit _) (unit _))).val.app (op V) φ)))).app
              (op (Over.mk (𝟙 (U.obj V)))))
      (e.hom.val.app (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app (unit _)).val.app (op V) m))) = _
    erw [← hn, he, he]
    change (((chart_unitHomIso (R := S) (unit _)).inv.val.app (op (U.obj V))
      (a.hom.app (op V) (h.hom.val.app (op V) φ))).app
        (op (Over.mk (𝟙 (U.obj V))))) (a.hom.app (op V) m) = _
    erw [chart_unitHomIso_inv_eval]
    dsimp only [h]
    erw [chart_unitHomIso_hom_eval]
    change a.hom.app (op V) m * a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op
      V))) = _
    rw [← map_mul]
    congr 1
    have hh := (φ.app (op (Over.mk (𝟙 V)))).hom.map_smul m (1 : R.obj.obj (op V))
    simpa only [smul_eq_mul, mul_one] using hh.symm
  have : IsIso (homObjMap (R := S) e.hom (𝟙 (unit _))) :=
    Functor.map_isIso ((homFunctor S).flip.obj (unit _)) e.hom.op
  rw [← hf]
  dsimp only [f]
  infer_instance

private lemma dualComparison_free_isIso
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify K AddCommGrpCat.{max u v w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (L : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (I : Type (max u v w)) [Finite I] (e : L ≅ free I) :
    IsIso (dualComparison.{u, v, w} (R := R) (S := S) a hcover L) := by
  let : HasFiniteBiproducts (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : HasFiniteBiproducts (SheafOfModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let DR := (homFunctor R).flip.obj (unit _)
  let DS := (homFunctor S).flip.obj (unit _)
  have hDR : DR.Additive :=
    { map_add := by
        intro X Y f g
        change homObjMap (f + g).unop (𝟙 _) = _
        rw [unop_add]
        exact hom_ext (PresheafOfModules.homObjMap_add_left f.unop.val g.unop.val (𝟙 _)) }
  have hDS : DS.Additive :=
    { map_add := by
        intro X Y f g
        change homObjMap (f + g).unop (𝟙 _) = _
        rw [unop_add]
        exact hom_ext (PresheafOfModules.homObjMap_add_left f.unop.val g.unop.val (𝟙 _)) }
  have hpush : (pushforward a).Additive :=
    { map_add := by intros; rfl }
  have hF : (pullback a).Additive :=
    (pullbackPushforwardAdjunction a).left_adjoint_additive
  let F := DR ⋙ pullback a
  let G := (pullback a).op ⋙ DS
  let α : F ⟶ G :=
    { app X := dualComparison.{u, v, w} (R := R) (S := S) a hcover X.unop
      naturality X Y f := dualComparison_natural.{u, v, w} (R := R) (S := S) a hcover Y.unop
        X.unop f.unop }
  have hunit : IsIso (α.app (op (unit _))) :=
    dualComparison_unit_isIso.{u, v, w} (R := R) (S := S) a hcover
  have hbi := comparison_biproduct F G α (unit _) I
  change IsIso (α.app (op L))
  rw [NatTrans.isIso_app_iff_of_iso α
    (e ≪≫ (biproduct.isoCoproduct fun _ : I ↦ unit _).symm).symm.op]
  exact hbi

end GlobalComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On a finite free chart the comparison defined by evaluation is invertible.
Source: Stacks Project, Modules on Sites, Tags 04J0, 0GMX and 0FNY.
(blueprint: lem-pur-ringed-site-pullback-dual-free-chart)

Restrict pullback to the slice using the canonical localization comparison.
Restriction of internal Hom identifies the two duals on that slice. Pairing-transfer
uniqueness identifies the transported map with the slice dual comparison. On the unit,
this comparison is the canonical pullback-unit isomorphism, by evaluation at one.
Both dual functors are additive, and pullback is additive as the left adjoint of an
additive functor. Naturality therefore gives invertibility on finite biproducts of
units. Transport along the supplied free trivialization and then back along the
localization and internal-Hom restriction isomorphisms. The empty biproduct handles
rank zero; no flatness or nonzero-ring hypothesis is needed. -/
theorem isIso_over_pullback_dual_of_free
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint)
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (d : (@pullback _ _ _ _ _ _ _ _ _ _ a hAdj).obj (homObj L (unit _)) ⟶
      homObj ((@pullback _ _ _ _ _ _ _ _ _ _ a hAdj).obj L) (unit _))
    (hd : ∀ (T : C) (φ : (homObj L (unit _)).val.obj (op T))
        (m : L.val.obj (op T)),
      (((d.val.app (op (U.obj T))
        (((@pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _ a hAdj).unit.app
          (homObj L (unit _))).val.app (op T) φ)).app
            (op (Over.mk (𝟙 (U.obj T))))))
        (((@pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _ a hAdj).unit.app L).val.app
          (op T) m) = a.hom.app (op T) (φ.app (op (Over.mk (𝟙 T))) m))
    (V : C) (r : ℕ)
    (he : Nonempty (L.over V ≅
      free (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)
        (ULift.{max u v w} (Fin r)))) :
    IsIso (d.over (U.obj V)) := by
  classical
  let := hAdj
  have hcont : ∀ T : C,
      (Over.post (X := T) U).IsContinuous (J.over T) (K.over (U.obj T)) :=
    fun T ↦ RingedSitePullback.local_continuous (U := U) _hcover T
  have := hcont
  let aV := RingedSitePullback.locMap a V
  have : (pushforward.{max u v w} aV).IsRightAdjoint :=
    module_pushforward_isRightAdjoint_of_universes.{max u v, v, max u v w}
      (J := J.over V) (K := K.over (U.obj V)) (U := Over.post U) aV
  let (T : Over V) : HasWeakSheafify ((J.over V).over T)
      AddCommGrpCat.{max u v w} :=
    by
      let := (coefficientSheafification.{max u v, v, max u v w} ((J.over V).over T)).1
      infer_instance
  let (T : Over V) : ((J.over V).over T).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w} :=
    (coefficientSheafification.{max u v, v, max u v w} ((J.over V).over T)).2
  obtain ⟨hK, hKW⟩ := coefficientSheafification.{max u v, v, max u v w} (K.over (U.obj V))
  let := hK
  let := hKW
  let hR := chart_overHomIso (R := R) L (unit _) V
  let hS := chart_overHomIso (R := S) ((pullback a).obj L) (unit _) (U.obj V)
  let cL := RingedSitePullback.localComparison a V L
  let cH := RingedSitePullback.localComparison a V (homObj L (unit _))
  have hcL : IsIso (homObjMap (R := S.over (U.obj V)) cL (𝟙 (unit _))) := by
    change IsIso (((homFunctor (S.over (U.obj V))).flip.obj (unit _)).map cL.op)
    infer_instance
  let dV := (pullback aV).map hR.inv ≫ cH ≫ d.over (U.obj V) ≫ hS.hom ≫
    homObjMap (R := S.over (U.obj V)) cL (𝟙 (unit _))
  have hdV : dV = dualComparison.{max u v, v, max u v w} (R := R.over V) (S := S.over (U.obj
    V)) aV (_hcover.overPost V) (L.over V) := by
    apply dualComparison_unique.{max u v, v, max u v w}
      (R := R.over V) (S := S.over (U.obj V)) aV (_hcover.overPost V) (L.over V)
    intro T φ m
    have hn := (pullbackPushforwardAdjunction aV).unit.naturality hR.inv
    have hnval := congrArg (fun f ↦ f.val.app (op T) φ) hn
    change ((hS.hom.val.app (op ((Over.post U).obj T))
      ((d.over (U.obj V)).val.app (op ((Over.post U).obj T))
        (cH.val.app (op ((Over.post U).obj T))
          (((pullback aV).map hR.inv).val.app (op ((Over.post U).obj T))
            (((pullbackPushforwardAdjunction aV).unit.app
              (homObj (R := R.over V) (L.over V) (unit _))).val.app (op T) φ))))).app
        (op (Over.mk (𝟙 ((Over.post U).obj T)))))
      (cL.val.app (op ((Over.post U).obj T))
        (((pullbackPushforwardAdjunction aV).unit.app (L.over V)).val.app (op T) m)) = _
    dsimp only [hS]
    rw [chart_overHomIso_hom_eval]
    erw [← hnval]
    dsimp only [Functor.id_map]
    change (((d.val.app (op (U.obj T.left))
      (cH.val.app (op ((Over.post U).obj T))
        (((pullbackPushforwardAdjunction aV).unit.app
          ((homObj (R := R) L (unit _)).over V)).val.app (op T)
            (hR.inv.val.app (op T) φ)))).app (op (Over.mk (𝟙 (U.obj T.left)))))
      (cL.val.app (op ((Over.post U).obj T))
        (((pullbackPushforwardAdjunction aV).unit.app (L.over V)).val.app (op T) m))) = _
    dsimp only [cH, cL]
    have hH := RingedSitePullback.localComparison_unit_apply.{u, v, w}
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      a V (homObj (R := R) L (unit _)) T (hR.inv.val.app (op T) φ)
    have hL := RingedSitePullback.localComparison_unit_apply.{u, v, w}
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V L T m
    exact (congrArg₂ (fun ψ x ↦
      ((d.val.app (op (U.obj T.left)) ψ).app (op (Over.mk (𝟙 (U.obj T.left))))) x)
      hH hL).trans ((hd T.left (hR.inv.val.app (op T) φ) m).trans
        (congrArg (a.hom.app (op T.left))
          (chart_overHomIso_inv_eval L (unit _) V T φ m)))
  obtain ⟨e⟩ := he
  have hdVIso : IsIso dV := by
    rw [hdV]
    exact dualComparison_free_isIso.{max u v, v, max u v w}
      (R := R.over V) (S := S.over (U.obj V)) aV (_hcover.overPost V) (L.over V) (ULift.{max u
        v w} (Fin r)) e
  have h₁ : IsIso (cH ≫ d.over (U.obj V) ≫ hS.hom ≫
      homObjMap (R := S.over (U.obj V)) cL (𝟙 (unit _))) :=
    IsIso.of_isIso_comp_left ((pullback aV).map hR.inv) _
  have h₂ : IsIso (d.over (U.obj V) ≫ hS.hom ≫
      homObjMap (R := S.over (U.obj V)) cL (𝟙 (unit _))) :=
    IsIso.of_isIso_comp_left cH _
  exact IsIso.of_isIso_comp_right (d.over (U.obj V))
    (hS.hom ≫ homObjMap (R := S.over (U.obj V)) cL (𝟙 (unit _)))

end SheafOfModules
