/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Coefficient comparison for global sections of inverse images
Source: Stacks Project, Tags 00YV, 03CB and 03CC.
(blueprint: lem-weil-pbc-abelian-pullback-global-sections-comparison). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private noncomputable def setPush {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)

private noncomputable def setAdj {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Scheme.etaleSetPullback f ⊣ setPush f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)

-- The coefficient map is the adjunction mate of the forgotten abelian unit.
-- Its value is fixed before any theorem asserting invertibility is used.
private noncomputable def forgetPullComparison {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G) ⟶
      (sheafForget Y.smallEtaleTopology).obj ((upperStar AddCommGrpCat.{u + 1} f).obj G) :=
   ((setAdj f).homEquiv
    ((sheafForget X.smallEtaleTopology).obj G)
    ((sheafForget Y.smallEtaleTopology).obj ((upperStar AddCommGrpCat.{u + 1} f).obj G))).symm
      ((sheafForget X.smallEtaleTopology).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem isIso_forgetPullComparison {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (forgetPullComparison f G) := by
  let q := forgetPullComparison f G
  obtain ⟨_, ea, da, Lr, ar, er, dr, hda, _, ha, _⟩ :=
    etaleInverseImageAlgebraicStructures Y X f
  have hd : da.hom.app ((upperStar AddCommGrpCat.{u + 1} f).obj G) = 𝟙 _ := by
    ext W x
    exact hda _ W x
  have he := ha G _ (𝟙 _)
  rw [Adjunction.homEquiv_id, hd] at he
  have hq : q = ea.inv.app G := by
    apply ((setAdj f).homEquiv _ _).injective
    dsimp only [q, forgetPullComparison]
    rw [Equiv.apply_symm_apply]
    change (sheafForget X.smallEtaleTopology).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G) ≫ 𝟙 _ =
        (setAdj f).homEquiv _ _ (ea.inv.app G ≫ 𝟙 _) at he
    simpa only [Functor.comp_obj, Functor.id_obj, Category.comp_id,
      Scheme.smallEtaleTopology, setAdj, setPush, lowerStar] using he
  change IsIso q
  rw [hq]
  infer_instance

private noncomputable def forgetPullIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G) ≅
      (sheafForget Y.smallEtaleTopology).obj ((upperStar AddCommGrpCat.{u + 1} f).obj G) := by
  have : IsIso (forgetPullComparison f G) := isIso_forgetPullComparison f G
  exact asIso (forgetPullComparison f G)

-- The following mate and section calculations specialize the proved argument in
-- WeilConjectures.AlgebraicGeometry.ModulePullbackSectionComparison to abelian groups.
private lemma forgetPullIso_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (setAdj f).unit.app ((sheafForget X.smallEtaleTopology).obj G) ≫
        (setPush f).map (forgetPullIso f G).hom =
      (sheafForget X.smallEtaleTopology).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G) := by
  exact ((setAdj f).homEquiv _ _).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma abelian_comp_unit {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
            ((upperStar AddCommGrpCat.{u + 1} f).obj G)) ≫
        (lowerStarComp AddCommGrpCat.{u + 1} h f).hom.app _ ≫
        (lowerStar AddCommGrpCat.{u + 1} (h ≫ f)).map
          ((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G) =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (h ≫ f)).unit.app G := by
  have hu := upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} h f G
  have hh := congrArg (fun t ↦ t ≫
    (lowerStar AddCommGrpCat.{u + 1} (h ≫ f)).map
      ((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G)) hu
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Adjunction.comp_unit_app] at hh
  rw [(lowerStar AddCommGrpCat.{u + 1} (h ≫ f)).map_id] at hh
  exact hh.symm.trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma abelian_pre_comp_unit {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
            ((upperStar AddCommGrpCat.{u + 1} f).obj G) ≫
            (lowerStar AddCommGrpCat.{u + 1} h).map
              ((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G)) =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (h ≫ f)).unit.app G ≫
        (lowerStarComp AddCommGrpCat.{u + 1} h f).inv.app _ := by
  apply (cancel_mono ((lowerStarComp AddCommGrpCat.{u + 1} h f).hom.app
    ((upperStar AddCommGrpCat.{u + 1} (h ≫ f)).obj G))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
  have hn := (lowerStarComp AddCommGrpCat.{u + 1} h f).hom.naturality
    ((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  exact (abelian_comp_unit h f G).trans (Category.comp_id _).symm

private noncomputable def setPushComp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    setPush h ⋙ setPush f ≅ setPush (h ≫ f) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).symm)
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)

private noncomputable def setPullComp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    Scheme.etaleSetPullback f ⋙ Scheme.etaleSetPullback h ≅
      Scheme.etaleSetPullback (h ≫ f) :=
  Classical.choose etaleSetInverseImageCompositionUnits.2.2 X Y Z f h

private lemma forget_push_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    {G H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : G ⟶ H) :
    (setPush f).map ((sheafForget Y.smallEtaleTopology).map a) =
      (sheafForget X.smallEtaleTopology).map ((lowerStar AddCommGrpCat.{u + 1} f).map a) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma forget_transition {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (forgetPullIso f G).hom ≫ (sheafForget Y.smallEtaleTopology).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
          ((upperStar AddCommGrpCat.{u + 1} f).obj G) ≫
          (lowerStar AddCommGrpCat.{u + 1} h).map
            ((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G)) =
      (setAdj h).unit.app
          ((Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G)) ≫
        (setPush h).map ((setPullComp h f).hom.app
          ((sheafForget X.smallEtaleTopology).obj G) ≫ (forgetPullIso (h ≫ f) G).hom) := by
  apply ((setAdj f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [forgetPullIso_unit]
  rw [forget_push_map, forget_push_map, ← Functor.map_comp, ← Functor.map_comp]
  rw [Category.assoc, ← Functor.map_comp, abelian_pre_comp_unit]
  -- Use the public composition-unit theorem directly; the analogous helper in
  -- ModulePullbackSectionComparison is private to that module.
  have hs : (setAdj f).unit.app ((sheafForget X.smallEtaleTopology).obj G) ≫
      (setPush f).map
        ((setAdj h).unit.app
          ((Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G)) ≫
          (setPush h).map ((setPullComp h f).hom.app
            ((sheafForget X.smallEtaleTopology).obj G))) =
      (setAdj (h ≫ f)).unit.app ((sheafForget X.smallEtaleTopology).obj G) ≫
        (setPushComp h f).inv.app
          ((Scheme.etaleSetPullback (h ≫ f)).obj
            ((sheafForget X.smallEtaleTopology).obj G)) := by
    ext U s
    obtain ⟨U⟩ := U
    exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      X Y Z f h ((sheafForget X.smallEtaleTopology).obj G) U s
  have hs' := congrArg (fun a ↦ a ≫
    (setPush f).map ((setPush h).map (forgetPullIso (h ≫ f) G).hom)) hs
  simp only [Functor.map_comp] at hs'
  dsimp only [Scheme.smallEtaleTopology] at *
  simp only [Category.assoc] at hs' ⊢
  rw [hs']
  have hn := (setPushComp h f).inv.naturality (forgetPullIso (h ≫ f) G).hom
  dsimp only [Functor.comp_map, Scheme.smallEtaleTopology] at hn
  rw [← hn, ← Category.assoc]
  have hu := forgetPullIso_unit (h ≫ f) G
  dsimp only [Scheme.smallEtaleTopology] at hu
  rw [hu, Functor.map_comp]
  rfl

private noncomputable def sectionEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale) :
    (((lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj G)).obj.obj (op U)) ≃
      (((Scheme.etaleSetPullback f).obj
        ((sheafForget X.smallEtaleTopology).obj G)).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) :=
  (((sheafToPresheaf Y.smallEtaleTopology (Type (u + 1))).mapIso
    (forgetPullIso f G).symm).app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))).toEquiv

private lemma forget_map_app (X : Scheme.{u})
    {G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : G ⟶ H) (U : X.Etaleᵒᵖ) (x : G.obj.obj U) :
    ((sheafForget X.smallEtaleTopology).map a).hom.app U x = a.hom.app U x := rfl


-- First establish the comparison on every site object, before terminal evaluation.
private theorem exists_abelianPullbackSectionComparison
    (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ e : ∀ (Y : Scheme.{u}) (f : Y ⟶ X) (U : X.Etale),
      (((lowerStar AddCommGrpCat.{u + 1} f).obj
        ((upperStar AddCommGrpCat.{u + 1} f).obj G)).obj.obj (op U)) ≃
      (((Scheme.etaleSetPullback f).obj
        ((sheafForget X.smallEtaleTopology).obj G)).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))),
      ∀ (Y Z : Scheme.{u}) (h : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X)
        (hk : h ≫ f = k) (U : X.Etale)
        (s : ((lowerStar AddCommGrpCat.{u + 1} f).obj
          ((upperStar AddCommGrpCat.{u + 1} f).obj G)).obj.obj (op U)),
        e Z k U
          ((((lowerStar AddCommGrpCat.{u + 1} f).map
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
              ((upperStar AddCommGrpCat.{u + 1} f).obj G)) ≫
            (lowerStarComp AddCommGrpCat.{u + 1} h f k hk.symm).hom.app _ ≫
            (lowerStar AddCommGrpCat.{u + 1} k).map
              ((upperStarComp AddCommGrpCat.{u + 1} h f k hk.symm).inv.app G)).hom.app
                (op U)) s) =
          etaleSetSectionComparison h f k hk
            ((sheafForget X.smallEtaleTopology).obj G) U (e Y f U s)  := by
  classical
  refine ⟨fun Y f U ↦ sectionEquiv f G U, ?_⟩
  intro Y Z h f k hk U s
  subst k
  have ht := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun a ↦ a.hom) (forget_transition h f G))
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))
    ((sectionEquiv f G U) s)
  have hf : (forgetPullIso f G).hom.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))
      (sectionEquiv f G U s) = s := (sectionEquiv f G U).symm_apply_apply s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply] at ht
  rw [hf] at ht
  have hm := forget_map_app Y
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
      ((upperStar AddCommGrpCat.{u + 1} f).obj G) ≫
      (lowerStar AddCommGrpCat.{u + 1} h).map
        ((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G))
    (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) s
  have ht := hm.symm.trans ht
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    AddCommGrpCat.comp_apply, lowerStar_map_hom_app, setPush,
    Functor.sheafPushforwardContinuous_map_hom_app, types_comp_apply] at ht
  let V := op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)
  let W := op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))
  let T := op ((MorphismProperty.Over.pullback @Etale ⊤ (h ≫ f)).obj U)
  let j : W ⟶ T :=
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app U).op
  let v := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
    ((upperStar AddCommGrpCat.{u + 1} f).obj G)).hom.app V s
  let t := ((setPullComp h f).hom.app ((sheafForget X.smallEtaleTopology).obj G)).hom.app W
    (((setAdj h).unit.app
      ((Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G))).hom.app V
        (sectionEquiv f G U s))
  have hn := ConcreteCategory.congr_hom
    (((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G).hom.naturality j) v
  have he := ConcreteCategory.congr_hom ((forgetPullIso (h ≫ f) G).inv.hom.naturality j)
    ((forgetPullIso (h ≫ f) G).hom.hom.app W t)
  have hc := Iso.hom_inv_id_apply
    (((sheafToPresheaf Z.smallEtaleTopology (Type (u + 1))).mapIso
      (forgetPullIso (h ≫ f) G)).app W) t
  change ((upperStarComp AddCommGrpCat.{u + 1} h f).inv.app G).hom.app W v =
    (forgetPullIso (h ≫ f) G).hom.hom.app W t at ht
  simp only [AddCommGrpCat.comp_apply] at hn
  simp only [types_comp_apply] at he
  change (forgetPullIso (h ≫ f) G).inv.hom.app W
    ((forgetPullIso (h ≫ f) G).hom.hom.app W t) = t at hc
  have result := (congrArg
    (fun x ↦ (forgetPullIso (h ≫ f) G).inv.hom.app T x) hn).trans
      ((congrArg (fun x ↦ (forgetPullIso (h ≫ f) G).inv.hom.app T
        (((upperStar AddCommGrpCat.{u + 1} (h ≫ f)).obj G).obj.map j x)) ht).trans
          (he.trans (congrArg
            (fun x ↦ ((Scheme.etaleSetPullback (h ≫ f)).obj
              ((sheafForget X.smallEtaleTopology).obj G)).obj.map j x) hc)))
  simp only [sectionEquiv, Iso.toEquiv, Iso.symm, Functor.mapIso, Iso.app,
    ObjectProperty.ι_map, lowerStar, lowerStarComp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    AddCommGrpCat.comp_apply, etaleSetSectionComparison, setPullComp,
    eqToHom_refl, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    types_comp_apply, types_id_apply, V, W, T, j, v, t, setAdj,
    Functor.comp_obj] at result ⊢
  convert result using 1


private noncomputable def terminalSectionEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ≃
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj (⊤_ X.Etale))) :=
  ((forget AddCommGrpCat.{u + 1}).mapIso
    ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).app G ≪≫
      G.obj.mapIso (PreservesTerminal.iso f.Etale).op)).toEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 2048 in
/-- Global sections of an abelian inverse image identify with sections of the set
inverse image on the base-changed terminal object, compatibly with composition.
There is no inverse system or finite-stage lifting assertion here.

Source: Stacks Project, Sites, Tags 00YV, 03CB and 03CC.
(blueprint: lem-weil-pbc-abelian-pullback-global-sections-comparison).

Proof: For each f, use etaleInverseImageAlgebraicStructures to obtain a natural
coefficient isomorphism C_f from the underlying abelian inverse image to the set
inverse image. Its direct-image comparison is the identity on sections and its
unit equation is R_f(C_f) composed with the forgotten abelian unit = the set unit.
Thus these choices are determined by the adjunction hom-set bijection, rather
than by an arbitrary isomorphism. Write T_f for the base change of the terminal
object and t_f : T_f ≅ terminal for PreservesTerminal.iso. Define e_f by the
Gamma-to-terminal-section isomorphism, then restriction along t_f.hom, then
C_f evaluated at T_f. All three maps are invertible, giving a bijection.

For h followed by f, apply the unit equation for C_h to the abelian inverse image
of F and that for C_f to F. Naturality of C_h transports the latter equation
through h inverse image. The resulting composite intertwines the composite
abelian unit with the composite set unit. The abelian composition isomorphism
is the mate of the direct-image composition comparison. The uniqueness clause
of etaleSetInverseImageCompositionUnits identifies its forgotten, conjugated
inverse with the chosen set composition map: both satisfy this same unit equation.
Evaluate this equality at the iterated base change of the terminal object.
Naturality in site objects moves C across the fibre-product pasting isomorphism;
uniqueness of terminal maps identifies the terminal-preservation maps on both
sides. Expanding globalSectionsUpperStarMap cancels the Gamma/terminal-section
isomorphisms. The remaining three factors are precisely the set unit, the set
composition map, and restriction along pullbackComp.hom, which define
etaleSetSectionComparison. Transport along hk gives the displayed equation.
For identities the same unit equations apply. On empty schemes or for the zero
sheaf both sets are singletons. No compactness, affineness, torsion, finiteness,
inverse system or finite-stage descent is used. -/
theorem exists_abelianPullbackGlobalSectionsComparison
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ e : ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} f).obj F)) ≃
      (((Scheme.etaleSetPullback f).obj
        ((sheafForget X.smallEtaleTopology).obj F)).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj (⊤_ X.Etale)))),
      ∀ (Y Z : Scheme.{u}) (h : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X)
        (hk : h ≫ f = k)
        (s : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((upperStar AddCommGrpCat.{u + 1} f).obj F)),
        e Z k ((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((upperStarComp AddCommGrpCat.{u + 1} h f k hk.symm).inv.app F)
          (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} h
            ((upperStar AddCommGrpCat.{u + 1} f).obj F) s)) =
        etaleSetSectionComparison h f k hk
          ((sheafForget X.smallEtaleTopology).obj F) (⊤_ X.Etale) (e Y f s) := by
  classical
  obtain ⟨e, he⟩ := exists_abelianPullbackSectionComparison X F
  refine ⟨fun Y f ↦ (terminalSectionEquiv f
    ((upperStar AddCommGrpCat.{u + 1} f).obj F)).trans (e Y f (⊤_ X.Etale)), ?_⟩
  intro Y Z h f k hk s
  dsimp only [Equiv.trans_apply]
  refine Eq.trans ?_ (he Y Z h f k hk (⊤_ X.Etale)
    (terminalSectionEquiv f ((upperStar AddCommGrpCat.{u + 1} f).obj F) s))
  apply congrArg (e Z k (⊤_ X.Etale))
  subst k
  let G := (upperStar AddCommGrpCat.{u + 1} f).obj F
  let H := (upperStar AddCommGrpCat.{u + 1} h).obj G
  let K := (upperStar AddCommGrpCat.{u + 1} (h ≫ f)).obj F
  let a : H ⟶ K := (upperStarComp AddCommGrpCat.{u + 1} h f).inv.app F
  let tf := PreservesTerminal.iso f.Etale
  let th := PreservesTerminal.iso h.Etale
  let tk := PreservesTerminal.iso (h ≫ f).Etale
  let j := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app
    (⊤_ X.Etale)
  let η := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app G
  let γY := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal)
  let γZ := (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal)
  change (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} h G ≫
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map a ≫
    γZ.hom.app K ≫ K.obj.map tk.hom.op) s =
      (γY.hom.app G ≫ G.obj.map tf.hom.op ≫ η.hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj (⊤_ X.Etale))) ≫
        H.obj.map j.op ≫ a.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (h ≫ f)).obj
            (⊤_ X.Etale)))) s
  apply ConcreteCategory.congr_hom
  have hγ := γZ.hom.naturality a
  have hα := a.hom.naturality tk.hom.op
  have hη := η.hom.naturality tf.hom.op
  change G.obj.map tf.hom.op ≫ η.hom.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj (⊤_ X.Etale))) =
      η.hom.app (op (⊤_ Y.Etale)) ≫ H.obj.map (h.Etale.map tf.hom).op at hη
  have hj : tk.hom ≫ th.inv = j ≫ h.Etale.map tf.hom := by
    apply (cancel_mono th.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Subsingleton.elim _ _
  -- Cancel global-section evaluation, then use naturality and terminal uniqueness.
  change globalSectionsUpperStarMap AddCommGrpCat.{u + 1} h G ≫
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map a ≫
    γZ.hom.app K ≫ K.obj.map tk.hom.op = _
  rw [← Category.assoc _ (γZ.hom.app K), hγ]
  change (γY.hom.app G ≫ η.hom.app (op (⊤_ Y.Etale)) ≫
    H.obj.map th.inv.op ≫ γZ.inv.app H) ≫
      (γZ.hom.app H ≫ a.hom.app (op (⊤_ Z.Etale))) ≫
        K.obj.map tk.hom.op = _
  simp only [Category.assoc]
  rw [← Category.assoc (γZ.inv.app H) (γZ.hom.app H), Iso.inv_hom_id_app]
  simp only [Category.id_comp]
  rw [← hα, ← Category.assoc (H.obj.map th.inv.op), ← H.obj.map_comp,
    ← op_comp, hj, op_comp, H.obj.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ (H.obj.map ((h.Etale).map tf.hom).op), ← hη]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.Etale
