/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Forgetting module coefficients in canonical pullback section comparisons

Source: Stacks Project, Sites, Tags 00X6, 00YV, 03CB, and 03CC, and module inverse
image, Tags 03D3 and 03D7.
(blueprint: lem-weil-pbc-module-pullback-section-comparison). -/

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

private noncomputable def forgetPullIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G) ≅
      (sheafForget Y.smallEtaleTopology).obj ((upperStar (ModuleCat.{u + 1} Λ) f).obj G) := by
  let q := ((setAdj f).homEquiv
    ((sheafForget X.smallEtaleTopology).obj G)
    ((sheafForget Y.smallEtaleTopology).obj ((upperStar (ModuleCat.{u + 1} Λ) f).obj G))).symm
      ((sheafForget X.smallEtaleTopology).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G))
  have : IsIso q := isIso_upperStar_forget_comparison Λ f G
  exact asIso q

private lemma forgetPullIso_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (setAdj f).unit.app ((sheafForget X.smallEtaleTopology).obj G) ≫
        (setPush f).map (forgetPullIso Λ f G).hom =
      (sheafForget X.smallEtaleTopology).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G) := by
  exact ((setAdj f).homEquiv _ _).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma module_comp_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G ≫
        (lowerStar (ModuleCat.{u + 1} Λ) f).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) h f).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (h ≫ f)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (h ≫ f)).unit.app G := by
  have hu := upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) h f G
  have hh := congrArg (fun t ↦ t ≫
    (lowerStar (ModuleCat.{u + 1} Λ) (h ≫ f)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G)) hu
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Adjunction.comp_unit_app] at hh
  rw [(lowerStar (ModuleCat.{u + 1} Λ) (h ≫ f)).map_id] at hh
  exact hh.symm.trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma module_pre_comp_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G ≫
        (lowerStar (ModuleCat.{u + 1} Λ) f).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
            (lowerStar (ModuleCat.{u + 1} Λ) h).map
              ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G)) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (h ≫ f)).unit.app G ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) h f).inv.app _ := by
  apply (cancel_mono ((lowerStarComp (ModuleCat.{u + 1} Λ) h f).hom.app
    ((upperStar (ModuleCat.{u + 1} Λ) (h ≫ f)).obj G))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
  have hn := (lowerStarComp (ModuleCat.{u + 1} Λ) h f).hom.naturality
    ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  exact (module_comp_unit Λ h f G).trans (Category.comp_id _).symm

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

private lemma set_comp_unit {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (setAdj f).unit.app G ≫ (setPush f).map
        ((setAdj h).unit.app ((Scheme.etaleSetPullback f).obj G) ≫
          (setPush h).map ((setPullComp h f).hom.app G)) =
      (setAdj (h ≫ f)).unit.app G ≫
        (setPushComp h f).inv.app ((Scheme.etaleSetPullback (h ≫ f)).obj G) := by
  ext U s
  obtain ⟨U⟩ := U
  exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1 X Y Z f h G U s

private lemma forget_push_map (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {G H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (a : G ⟶ H) :
    (setPush f).map ((sheafForget Y.smallEtaleTopology).map a) =
      (sheafForget X.smallEtaleTopology).map ((lowerStar (ModuleCat.{u + 1} Λ) f).map a) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma forget_transition (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (forgetPullIso Λ f G).hom ≫ (sheafForget Y.smallEtaleTopology).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
          ((upperStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) h).map
            ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G)) =
      (setAdj h).unit.app
          ((Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G)) ≫
        (setPush h).map ((setPullComp h f).hom.app
          ((sheafForget X.smallEtaleTopology).obj G) ≫ (forgetPullIso Λ (h ≫ f) G).hom) := by
  apply ((setAdj f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [forgetPullIso_unit]
  rw [forget_push_map, forget_push_map, ← Functor.map_comp, ← Functor.map_comp]
  rw [Category.assoc, ← Functor.map_comp, module_pre_comp_unit]
  have hs := set_comp_unit h f ((sheafForget X.smallEtaleTopology).obj G)
  have hs' := congrArg (fun a ↦ a ≫
    (setPush f).map ((setPush h).map (forgetPullIso Λ (h ≫ f) G).hom)) hs
  simp only [Functor.map_comp] at hs'
  dsimp only [Scheme.smallEtaleTopology] at *
  simp only [Category.assoc] at hs' ⊢
  rw [hs']
  have hn := (setPushComp h f).inv.naturality (forgetPullIso Λ (h ≫ f) G).hom
  dsimp only [Functor.comp_map, Scheme.smallEtaleTopology] at hn
  rw [← hn, ← Category.assoc]
  have hu := forgetPullIso_unit Λ (h ≫ f) G
  dsimp only [Scheme.smallEtaleTopology] at hu
  rw [hu, Functor.map_comp]
  rfl

private noncomputable def sectionEquiv (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etale) :
    (((lowerStar (ModuleCat.{u + 1} Λ) f).obj
      ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)).obj.obj (op U)) ≃
      (((Scheme.etaleSetPullback f).obj
        ((sheafForget X.smallEtaleTopology).obj G)).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) :=
  (((sheafToPresheaf Y.smallEtaleTopology (Type (u + 1))).mapIso
    (forgetPullIso Λ f G).symm).app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))).toEquiv

private lemma forget_map_app (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : G ⟶ H) (U : X.Etaleᵒᵖ) (x : G.obj.obj U) :
    ((sheafForget X.smallEtaleTopology).map a).hom.app U x = a.hom.app U x := rfl

/-- The underlying sections of a module inverse image identify with those of the
set inverse image, compatibly with the canonical unit/composition maps. There is no
scheme limit, directed index, or colimit assertion in this comparison.

Source: Stacks Project, Sites, Tags 00X6, 00YV, 03CB, and 03CC; module inverse image,
Tags 03D3 and 03D7.
(blueprint: lem-weil-pbc-module-pullback-section-comparison)

Proof: Start with the abelian inverse image and its unit-compatible underlying-set
comparison. For a module sheaf G, let λ_r be its scalar-r endomorphism. Give the
abelian inverse image the scalar maps obtained by applying abelian inverse image
to λ_r. Additivity preserves λ_(r+r') = λ_r + λ_r', and functoriality preserves
λ_(rr') = λ_r ≫ λ_r', λ_1 = identity, and λ_0 = zero. Thus these maps give a sheaf
of Λ-modules. Naturality of the abelian unit and counit makes both Λ-linear.
The abelian adjunction restricts to Λ-linear maps: its hom-set bijection takes
precomposition with λ_r to precomposition with its inverse image, and
postcomposition with λ_r to postcomposition with its direct image. Consequently
the transported module inverse image is left adjoint to the recorded module
direct image. Uniqueness of left adjoints identifies it with upperStar of
ModuleCat, compatibly with the unit. Compose this comparison with the abelian-to-set
comparison and evaluate at the base change of U to obtain the equivalences e.
Direct images are precomposition and commute with forgetting on the nose. Their
composition comparisons are restriction along the same fibre-product pasting
isomorphism. The inverse-image composition comparison is the unique mate of that
direct-image comparison, determined by its unit equation. Therefore forgetting
carries it to the set composition comparison chosen in
etaleSetInverseImageCompositionUnits. Naturality in the sheaf and the site object
identifies the unit, the composition comparison, and the restriction along the
pasting isomorphism factor by factor. These are the three factors defining
etaleSetSectionComparison and the displayed module composite, giving the equation.
Transport along hk uses the same equality on both sides.

Edge cases: identities give the same identity/unit comparison. Empty objects and
the zero module sheaf have singleton underlying section sets, so the equation
still holds. No affineness, quasi-compactness, torsion, or finite-generation
assumption is needed. -/
theorem exists_modulePullbackSectionComparison
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : ∀ (Y : Scheme.{u}) (f : Y ⟶ X) (U : X.Etale),
      (((lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)).obj.obj (op U)) ≃
      (((Scheme.etaleSetPullback f).obj
        ((sheafForget X.smallEtaleTopology).obj G)).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))),
      ∀ (Y Z : Scheme.{u}) (h : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X)
        (hk : h ≫ f = k) (U : X.Etale)
        (s : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
          ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)).obj.obj (op U)),
        e Z k U
          ((((lowerStar (ModuleCat.{u + 1} Λ) f).map
            ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
              ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)) ≫
            (lowerStarComp (ModuleCat.{u + 1} Λ) h f k hk.symm).hom.app _ ≫
            (lowerStar (ModuleCat.{u + 1} Λ) k).map
              ((upperStarComp (ModuleCat.{u + 1} Λ) h f k hk.symm).inv.app G)).hom.app
                (op U)) s) =
          etaleSetSectionComparison h f k hk
            ((sheafForget X.smallEtaleTopology).obj G) U (e Y f U s)  := by
  classical
  refine ⟨fun Y f U ↦ sectionEquiv Λ f G U, ?_⟩
  intro Y Z h f k hk U s
  subst k
  have ht := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun a ↦ a.hom) (forget_transition Λ h f G))
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))
    ((sectionEquiv Λ f G U) s)
  have hf : (forgetPullIso Λ f G).hom.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))
      (sectionEquiv Λ f G U s) = s := (sectionEquiv Λ f G U).symm_apply_apply s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply] at ht
  rw [hf] at ht
  have hm := forget_map_app Λ Y
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
      ((upperStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) h).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G))
    (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) s
  have ht := hm.symm.trans ht
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply, lowerStar_map_hom_app, setPush,
    Functor.sheafPushforwardContinuous_map_hom_app, types_comp_apply] at ht
  let V := op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)
  let W := op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))
  let T := op ((MorphismProperty.Over.pullback @Etale ⊤ (h ≫ f)).obj U)
  let j : W ⟶ T :=
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app U).op
  let v := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
    ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)).hom.app V s
  let t := ((setPullComp h f).hom.app ((sheafForget X.smallEtaleTopology).obj G)).hom.app W
    (((setAdj h).unit.app
      ((Scheme.etaleSetPullback f).obj ((sheafForget X.smallEtaleTopology).obj G))).hom.app V
        (sectionEquiv Λ f G U s))
  have hn := ConcreteCategory.congr_hom
    (((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G).hom.naturality j) v
  have he := ConcreteCategory.congr_hom ((forgetPullIso Λ (h ≫ f) G).inv.hom.naturality j)
    ((forgetPullIso Λ (h ≫ f) G).hom.hom.app W t)
  have hc := Iso.hom_inv_id_apply
    (((sheafToPresheaf Z.smallEtaleTopology (Type (u + 1))).mapIso
      (forgetPullIso Λ (h ≫ f) G)).app W) t
  change ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G).hom.app W v =
    (forgetPullIso Λ (h ≫ f) G).hom.hom.app W t at ht
  simp only [ModuleCat.comp_apply] at hn
  simp only [types_comp_apply] at he
  change (forgetPullIso Λ (h ≫ f) G).inv.hom.app W
    ((forgetPullIso Λ (h ≫ f) G).hom.hom.app W t) = t at hc
  have result := (congrArg
    (fun x ↦ (forgetPullIso Λ (h ≫ f) G).inv.hom.app T x) hn).trans
      ((congrArg (fun x ↦ (forgetPullIso Λ (h ≫ f) G).inv.hom.app T
        (((upperStar (ModuleCat.{u + 1} Λ) (h ≫ f)).obj G).obj.map j x)) ht).trans
          (he.trans (congrArg
            (fun x ↦ ((Scheme.etaleSetPullback (h ≫ f)).obj
              ((sheafForget X.smallEtaleTopology).obj G)).obj.map j x) hc)))
  simp only [sectionEquiv, Iso.toEquiv, Iso.symm, Functor.mapIso, Iso.app,
    ObjectProperty.ι_map, lowerStar, lowerStarComp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    ModuleCat.comp_apply, etaleSetSectionComparison, setPullComp,
    eqToHom_refl, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    types_comp_apply, types_id_apply, V, W, T, j, v, t, setAdj,
    Functor.comp_obj] at result ⊢
  convert result using 1

end AlgebraicGeometry.Etale
