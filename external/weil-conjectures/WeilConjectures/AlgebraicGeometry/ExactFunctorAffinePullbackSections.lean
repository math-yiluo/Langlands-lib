/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.AlgebraicGeometry.ExactFunctorAffineEtaleSheafification
import WeilConjectures.SixFunctors.BaseChange.GlobalSections

/-! # Coefficient change and sections of inverse images -/

@[expose] public section

universe a b u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  (L : B ⥤ A) (U : A ⥤ B) (adj : L ⊣ U)

noncomputable def coefficientPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar B f ⋙ Sheaf.composeAndSheafify X.smallEtaleTopology L ≅
      Sheaf.composeAndSheafify Y.smallEtaleTopology L ⋙ upperStar A f := by
  letI := adj.isRightAdjoint
  let adjX := Sheaf.adjunction X.smallEtaleTopology adj
  let adjY := Sheaf.adjunction Y.smallEtaleTopology adj
  exact ((upperStarLowerStarAdjunction B f).comp adjX).leftAdjointUniq
    (adjY.comp (upperStarLowerStarAdjunction A f))

private theorem coefficientPullbackIso_conjugate [U.IsRightAdjoint]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    conjugateEquiv
      ((Sheaf.adjunction Y.smallEtaleTopology adj).comp (upperStarLowerStarAdjunction A f))
      ((upperStarLowerStarAdjunction B f).comp (Sheaf.adjunction X.smallEtaleTopology adj))
      (coefficientPullbackIso L U adj f).hom = 𝟙 _ := by
  simp only [coefficientPullbackIso, Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv]
  erw [Equiv.apply_symm_apply]
  rfl

private theorem coefficientPullbackIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology B) (V : Y.Etale) :
    ((upperStarLowerStarAdjunction B f).unit.app F).hom.app (op V) ≫
        adj.unit.app (((upperStar B f).obj F).obj.obj (op (f.Etale.obj V))) ≫
        U.map ((toSheafify X.smallEtaleTopology
          (((upperStar B f).obj F).obj ⋙ L)).app (op (f.Etale.obj V))) ≫
        U.map (((coefficientPullbackIso L U adj f).hom.app F).hom.app
          (op (f.Etale.obj V))) =
      adj.unit.app (F.obj.obj (op V)) ≫
        U.map ((toSheafify Y.smallEtaleTopology (F.obj ⋙ L)).app (op V)) ≫
        U.map (((upperStarLowerStarAdjunction A f).unit.app
          ((Sheaf.composeAndSheafify Y.smallEtaleTopology L).obj F)).hom.app (op V)) := by
  let := adj.isRightAdjoint
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((upperStarLowerStarAdjunction B f).comp (Sheaf.adjunction X.smallEtaleTopology adj))
    ((Sheaf.adjunction Y.smallEtaleTopology adj).comp (upperStarLowerStarAdjunction A f)) F
  have h' := congrArg (fun η ↦ η.hom.app (op V)) h
  simpa only [coefficientPullbackIso, Adjunction.comp_unit_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStar_map_hom_app,
    sheafCompose_map_hom, Functor.comp_map, Functor.whiskerRight_app,
    Sheaf.adjunction_unit_app_hom, Adjunction.whiskerRight_unit_app_app, Scheme.Hom.Etale,
    Category.assoc] using h'

private theorem coefficientPullbackIso_eval_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology B) (V : Y.Etale) :
    L.map (((upperStarLowerStarAdjunction B f).unit.app F).hom.app (op V)) ≫
        (toSheafify X.smallEtaleTopology
          (((upperStar B f).obj F).obj ⋙ L)).app (op (f.Etale.obj V)) ≫
        (((coefficientPullbackIso L U adj f).hom.app F).hom.app
          (op (f.Etale.obj V))) =
      (toSheafify Y.smallEtaleTopology (F.obj ⋙ L)).app (op V) ≫
        (((upperStarLowerStarAdjunction A f).unit.app
          ((Sheaf.composeAndSheafify Y.smallEtaleTopology L).obj F)).hom.app (op V)) := by
  apply (adj.homEquiv (F.obj.obj (op V)) _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := adj.unit.naturality
    (((upperStarLowerStarAdjunction B f).unit.app F).hom.app (op V))
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    lowerStar_obj_val_obj, Scheme.Hom.Etale] at hn ⊢
  rw [← reassoc_of% hn]
  exact coefficientPullbackIso_unit L U adj f F V

noncomputable def coefficientSectionsIso (X : Scheme.{u}) [IsAffine X]
    [PreservesFiniteLimits L] (F : Sheaf X.smallEtaleTopology B) :
    L.obj ((Sheaf.Γ X.smallEtaleTopology B).obj F) ≅
      (Sheaf.Γ X.smallEtaleTopology A).obj
        ((Sheaf.composeAndSheafify X.smallEtaleTopology L).obj F) := by
  let V : X.Etale := ⊤_ X.Etale
  let t : IsTerminal V := terminalIsTerminal
  have : IsIso V.hom := isIso_terminal_hom X
  have : IsAffine V.left := @isAffine_of_isAffineHom V.left X V.hom inferInstance inferInstance
  have := Scheme.exactFunctor_affine_toSheafify_isIso X F L V
  exact L.mapIso ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology B t).app F) ≪≫
    asIso ((toSheafify X.smallEtaleTopology (F.obj ⋙ L)).app (op V)) ≪≫
    ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A t).app _).symm

noncomputable def coefficientPullbackSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [PreservesFiniteLimits L] (F : Sheaf Y.smallEtaleTopology B) :
    L.obj ((Sheaf.Γ X.smallEtaleTopology B).obj ((upperStar B f).obj F)) ≅
      (Sheaf.Γ X.smallEtaleTopology A).obj ((upperStar A f).obj
        ((Sheaf.composeAndSheafify Y.smallEtaleTopology L).obj F)) :=
  coefficientSectionsIso L X ((upperStar B f).obj F) ≪≫
    (Sheaf.Γ X.smallEtaleTopology A).mapIso ((coefficientPullbackIso L U adj f).app F)

private theorem coefficientSectionsIso_naturality (X : Scheme.{u}) [IsAffine X]
    [PreservesFiniteLimits L] {F F' : Sheaf X.smallEtaleTopology B} (α : F ⟶ F') :
    L.map ((Sheaf.Γ X.smallEtaleTopology B).map α) ≫
        (coefficientSectionsIso L X F').hom =
      (coefficientSectionsIso L X F).hom ≫
        (Sheaf.Γ X.smallEtaleTopology A).map
          ((Sheaf.composeAndSheafify X.smallEtaleTopology L).map α) := by
  let V : X.Etale := ⊤_ X.Etale
  let t : IsTerminal V := terminalIsTerminal
  let eB := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology B t
  let eA := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A t
  change L.map ((Sheaf.Γ _ B).map α) ≫ L.map (eB.hom.app F') ≫ _ ≫ eA.inv.app _ =
    (L.map (eB.hom.app F) ≫ _ ≫ eA.inv.app _) ≫ (Sheaf.Γ _ A).map _
  rw [← L.map_comp_assoc, eB.hom.naturality, L.map_comp, Category.assoc,
    Category.assoc]
  simp only [Category.assoc, asIso_hom]
  rw [← eA.inv.naturality]
  have hh := congrArg (fun η ↦ η.app (op V))
    (toSheafify_naturality X.smallEtaleTopology (Functor.whiskerRight α.hom L))
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hh
  change L.map (eB.hom.app F) ≫ L.map (α.hom.app (op V)) ≫
      (toSheafify _ (F'.obj ⋙ L)).app (op V) ≫ eA.inv.app _ =
    L.map (eB.hom.app F) ≫ (toSheafify _ (F.obj ⋙ L)).app (op V) ≫
      (sheafifyMap _ (Functor.whiskerRight α.hom L)).app (op V) ≫ eA.inv.app _
  rw [reassoc_of% hh]

/-- Canonical pullback of sections, with a specified composite structure map. -/
noncomputable def pullbackSectionMap {S X Y : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) (h : X ⟶ Y) (f : Y ⟶ S)
    (g : X ⟶ S) (w : g = h ≫ f) :
    (Sheaf.Γ Y.smallEtaleTopology A).obj ((upperStar A f).obj F) ⟶
      (Sheaf.Γ X.smallEtaleTopology A).obj ((upperStar A g).obj F) :=
  globalSectionsUpperStarMap A h ((upperStar A f).obj F) ≫
    (Sheaf.Γ X.smallEtaleTopology A).map ((upperStarComp A h f g w).inv.app F)

@[reassoc]
private theorem globalSectionsUpperStarMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology A} (α : F ⟶ F') :
    (Sheaf.Γ Y.smallEtaleTopology A).map α ≫ globalSectionsUpperStarMap A f F' =
      globalSectionsUpperStarMap A f F ≫
        (Sheaf.Γ X.smallEtaleTopology A).map ((upperStar A f).map α) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      terminalIsTerminal).hom.naturality_assoc α]
  have hn := (upperStarLowerStarAdjunction A f).unit.naturality α
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar A f).map α).hom.naturality
    (PreservesTerminal.iso (Scheme.Hom.Etale f)).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
      terminalIsTerminal).inv.app ((upperStar A f).obj F')) hu.symm

@[reassoc]
theorem pullbackSectionMap_naturality {S X Y : Scheme.{u}}
    {F F' : Sheaf S.smallEtaleTopology A} (α : F ⟶ F')
    (h : X ⟶ Y) (f : Y ⟶ S) (g : X ⟶ S) (w : g = h ≫ f) :
    (Sheaf.Γ Y.smallEtaleTopology A).map ((upperStar A f).map α) ≫
        pullbackSectionMap F' h f g w =
      pullbackSectionMap F h f g w ≫
        (Sheaf.Γ X.smallEtaleTopology A).map ((upperStar A g).map α) := by
  unfold pullbackSectionMap
  rw [globalSectionsUpperStarMap_naturality_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg ((Sheaf.Γ X.smallEtaleTopology A).map)
    ((upperStarComp A h f g w).inv.naturality α)

theorem pullbackSectionMap_id {S X : Scheme.{u}} (F : Sheaf S.smallEtaleTopology A)
    (f : X ⟶ S) : pullbackSectionMap F (𝟙 X) f f (by simp) = 𝟙 _ := by
  unfold pullbackSectionMap
  rw [upperStarComp_id_left]
  simpa using globalSectionsUpperStarMap_id A ((upperStar A f).obj F)

@[reassoc]
theorem pullbackSectionMap_comp {S X Y Z : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) (h : X ⟶ Y) (k : Y ⟶ Z)
    (f : Z ⟶ S) (g : Y ⟶ S) (l : X ⟶ S)
    (wg : g = k ≫ f) (wl : l = h ≫ g) :
    pullbackSectionMap F k f g wg ≫ pullbackSectionMap F h g l wl =
      pullbackSectionMap F (h ≫ k) f l (by rw [wl, wg, Category.assoc]) := by
  subst wg
  subst wl
  unfold pullbackSectionMap
  rw [Category.assoc, globalSectionsUpperStarMap_naturality_assoc,
    ← globalSectionsUpperStarMap_comp_assoc]
  simp only [← Functor.map_comp]
  congr 1
  have he := congrArg (fun e ↦ e.inv.app F) (upperStarComp_assoc A h k f)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp] at he
  rw [he]
  simp


private theorem coefficientPullbackIso_comp [U.IsRightAdjoint]
    {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S) (g : X ⟶ S)
    (w : g = h ≫ f) :
    Functor.whiskerRight (upperStarComp B h f g w).inv
        (Sheaf.composeAndSheafify X.smallEtaleTopology L) ≫
        (coefficientPullbackIso L U adj g).hom =
      (Functor.associator (upperStar B f) (upperStar B h)
        (Sheaf.composeAndSheafify X.smallEtaleTopology L)).hom ≫
      Functor.whiskerLeft (upperStar B f) (coefficientPullbackIso L U adj h).hom ≫
      (Functor.associator (upperStar B f)
        (Sheaf.composeAndSheafify Y.smallEtaleTopology L) (upperStar A h)).inv ≫
      Functor.whiskerRight (coefficientPullbackIso L U adj f).hom (upperStar A h) ≫
      (Functor.associator (Sheaf.composeAndSheafify S.smallEtaleTopology L)
        (upperStar A f) (upperStar A h)).hom ≫
      Functor.whiskerLeft (Sheaf.composeAndSheafify S.smallEtaleTopology L)
        (upperStarComp A h f g w).inv := by
  let ax := Sheaf.adjunction X.smallEtaleTopology adj
  let ay := Sheaf.adjunction Y.smallEtaleTopology adj
  let az := Sheaf.adjunction S.smallEtaleTopology adj
  let bf := upperStarLowerStarAdjunction B f
  let bh := upperStarLowerStarAdjunction B h
  let bg := upperStarLowerStarAdjunction B g
  let af := upperStarLowerStarAdjunction A f
  let ah := upperStarLowerStarAdjunction A h
  let ag := upperStarLowerStarAdjunction A g
  let a0 := (bf.comp bh).comp ax
  let a1 := bf.comp (bh.comp ax)
  let a2 := bf.comp (ay.comp ah)
  let a3 := (bf.comp ay).comp ah
  let a4 := (az.comp af).comp ah
  let a5 := az.comp (af.comp ah)
  let a6 := az.comp ag
  have hb : conjugateEquiv bg (bf.comp bh) (upperStarComp B h f g w).inv =
      (lowerStarComp B h f g w).inv :=
    congrArg Iso.inv (conjugateIsoEquiv_upperStarComp B h f g w)
  have ha : conjugateEquiv ag (af.comp ah) (upperStarComp A h f g w).inv =
      (lowerStarComp A h f g w).inv :=
    congrArg Iso.inv (conjugateIsoEquiv_upperStarComp A h f g w)
  have hi : conjugateEquiv a3 a2
      (Functor.associator (upperStar B f)
        (Sheaf.composeAndSheafify Y.smallEtaleTopology L) (upperStar A h)).inv =
      (Functor.associator (lowerStar A h) (sheafCompose Y.smallEtaleTopology U)
        (lowerStar B f)).inv := by
    have hh := conjugateEquiv_associator_hom bf ay ah
    have he : conjugateIsoEquiv a2 a3
        (Functor.associator (upperStar B f)
          (Sheaf.composeAndSheafify Y.smallEtaleTopology L) (upperStar A h)) =
        Functor.associator (lowerStar A h) (sheafCompose Y.smallEtaleTopology U)
          (lowerStar B f) := Iso.ext hh
    exact congrArg Iso.inv he
  apply (conjugateEquiv a6 a0).injective
  have hl : conjugateEquiv a6 a0
      (Functor.whiskerRight (upperStarComp B h f g w).inv
        (Sheaf.composeAndSheafify X.smallEtaleTopology L) ≫
        (coefficientPullbackIso L U adj g).hom) =
      Functor.whiskerLeft (sheafCompose X.smallEtaleTopology U)
        (lowerStarComp B h f g w).inv := by
    rw [← conjugateEquiv_comp a6 (bg.comp ax) a0,
      coefficientPullbackIso_conjugate, Category.id_comp,
      conjugateEquiv_whiskerRight bg (bf.comp bh) ax, hb]
  rw [hl]
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp a6 a5 a0, ← conjugateEquiv_comp a5 a4 a0,
    ← conjugateEquiv_comp a4 a3 a0, ← conjugateEquiv_comp a3 a2 a0,
    ← conjugateEquiv_comp a2 a1 a0]
  rw [conjugateEquiv_whiskerLeft ag (af.comp ah) az, ha,
    conjugateEquiv_associator_hom az af ah,
    conjugateEquiv_whiskerRight (az.comp af) (bf.comp ay) ah,
    coefficientPullbackIso_conjugate, hi,
    conjugateEquiv_whiskerLeft (ay.comp ah) (bh.comp ax) bf,
    coefficientPullbackIso_conjugate, conjugateEquiv_associator_hom bf bh ax]
  ext M V
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  change _ = U.map (((lowerStarComp A h f g w).inv.app M).hom.app V) ≫
    𝟙 _ ≫ 𝟙 _
  simp only [Category.comp_id]
  simp only [Functor.comp_obj, sheafCompose, lowerStarComp,
    Functor.sheafPushforwardContinuousComp', Iso.trans_inv,
    Functor.sheafPushforwardContinuousIso_inv, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
    ObjectProperty.lift_obj_obj, Functor.whiskeringRight_obj_obj, Functor.whiskerRight_app,
    Functor.op_obj, NatTrans.op_app, Functor.comp_map,
    Functor.sheafPushforwardContinuousComp_inv_app_hom_app, U.map_comp]
  erw [U.map_id]
  rfl

private theorem coefficientSectionsIso_pullback {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [PreservesFiniteLimits L]
    (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology B) :
    L.map (globalSectionsUpperStarMap B f F) ≫
        (coefficientSectionsIso L X ((upperStar B f).obj F)).hom ≫
        (Sheaf.Γ X.smallEtaleTopology A).map
          ((coefficientPullbackIso L U adj f).hom.app F) =
      (coefficientSectionsIso L Y F).hom ≫
        globalSectionsUpperStarMap A f
          ((Sheaf.composeAndSheafify Y.smallEtaleTopology L).obj F) := by
  let H := (upperStar B f).obj F
  let E := (coefficientPullbackIso L U adj f).hom.app F
  let r := (PreservesTerminal.iso f.Etale).inv.op
  have ht := (toSheafify X.smallEtaleTopology (H.obj ⋙ L)).naturality r
  have he := E.hom.naturality r
  simp only [Functor.comp_map] at ht
  dsimp only [H, r, E] at ht he
  have hu := coefficientPullbackIso_eval_unit L U adj f F (⊤_ Y.Etale)
  simp only [coefficientSectionsIso, globalSectionsUpperStarMap, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.app_hom, Iso.app_inv]
  rw [← (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
    terminalIsTerminal).inv.naturality]
  simp only [← L.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [L.map_comp, Category.assoc, Sheaf.composeAndSheafify,
    Functor.comp_obj, ObjectProperty.ι_obj]
  erw [L.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% ht, reassoc_of% he, reassoc_of% hu]
  simp

/-- Exact coefficient change commutes with the canonical maps on affine pullback sections.
Source: Stacks, Sites, Tag 0738(4), and the inverse-image adjunction.
Proof: the pullback comparison is the unique isomorphism between the two left adjoints
of the objectwise commuting direct-image/coefficient right adjoints. Its unit equation,
evaluated at the terminal object, identifies the two maps on sections. For a composite,
apply the same equation to the composite adjunction. Uniqueness of transposes identifies
the two routes with the inverse-image composition comparison. The affine sheafification
comparison is natural, because it is the sheafification unit evaluated on an affine object.
(auxiliary; not a blueprint node) -/
theorem coefficientPullbackSectionsIso_comp {S X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [PreservesFiniteLimits L]
    (F : Sheaf S.smallEtaleTopology B) (h : X ⟶ Y) (f : Y ⟶ S)
    (g : X ⟶ S) (w : g = h ≫ f) :
    L.map (pullbackSectionMap F h f g w) ≫
        (coefficientPullbackSectionsIso L U adj g F).hom =
      (coefficientPullbackSectionsIso L U adj f F).hom ≫
        pullbackSectionMap ((Sheaf.composeAndSheafify S.smallEtaleTopology L).obj F)
          h f g w := by
  let := adj.isRightAdjoint
  have hc := congrArg (fun η ↦ η.app F) (coefficientPullbackIso_comp L U adj h f g w)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp] at hc
  unfold pullbackSectionMap coefficientPullbackSectionsIso
  simp only [L.map_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% (coefficientSectionsIso_naturality L X
    ((upperStarComp B h f g w).inv.app F))]
  simp only [← Functor.map_comp]
  erw [hc]
  simp only [Functor.map_comp]
  rw [reassoc_of% (coefficientSectionsIso_pullback L U adj h
    ((upperStar B f).obj F))]
  rw [← globalSectionsUpperStarMap_naturality_assoc]
  rfl


end AlgebraicGeometry.Etale
