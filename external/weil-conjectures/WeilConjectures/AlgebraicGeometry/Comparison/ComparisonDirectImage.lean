/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-!
# The canonical comparison for bounded below direct images

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
theorem-comparison-direct-images--1; Stacks Project, Tag 099R
(blueprint: theorem-comparison-direct-images--1).

The comparison is the existing derived base-change transformation of the canonical
underived mate. The three statements give invertibility, identity compatibility and
composition compatibility. Naturality in the complex is built into the transformation.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical derived composition identification on Etale sheaves, with the
injective-preservation instance supplied by the exact inverse-image adjunction.
Source: blueprint theorem-comparison-direct-images--1, final proof paragraph;
Stacks, Tag 099R (blueprint: theorem-comparison-direct-images--1). -/
noncomputable def etaleComparisonDirectImageCompIso (Λ : Type (u + 1)) [Ring Λ]
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus ≅
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)).rightDerivedFunctorPlus :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  Functor.rightDerivedFunctorPlusCompIso'
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g)
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f g)

/-- The canonical derived composition identification on ProEtale sheaves, with the
injective-preservation instance supplied by the exact inverse-image adjunction.
Source: blueprint theorem-comparison-direct-images--1, final proof paragraph;
Stacks, Tag 099R (blueprint: theorem-comparison-direct-images--1). -/
noncomputable def proEtaleComparisonDirectImageCompIso (Λ : Type (u + 1)) [Ring Λ]
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus ≅
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)).rightDerivedFunctorPlus :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  Functor.rightDerivedFunctorPlusCompIso'
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) g)
    (ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) f g)

/-- The canonical comparison for a quasi-compact quasi-separated morphism is invertible.
Source: blueprint theorem-comparison-direct-images--1; Stacks, Tag 099R
(blueprint: theorem-comparison-direct-images--1).

Proof: take the mate of the pulled-back etale counit using the pullback comparison.
Exact inverse images and bounded below injective representatives keep both sides in D+.
Localize on affine opens of the target; restriction preserves injectives on both sites.
On an affine ind-etale basis object W = lim W_i, apply derived cohomology continuity
first to W_i and then to U times_V W_i. Quasi-compactness and quasi-separatedness of the
morphism give qcqs stage schemes and affine transition maps. Fixing one index gives the
fixed-stage complexes required by continuity. Derived evaluation of direct image identifies
the middle groups. Global cohomology comparison and pro-etale restriction identify the
result with derived sections of the target. To check this is the specified map, represent
L by etale injectives I and resolve its comparison pullback by pro-etale injectives J.
Comparison pullbacks of injectives are section-acyclic on the basis, so the source section
complex computes derived sections. The comparison-sections formula expresses it as a
filtered colimit of sections of I; exact filtered colimits commute with cohomology. At each
finite stage the counit is identity on sections, so its restriction is precisely the map
used by continuity. Thus the specified mate induces the computed isomorphisms, and basis
derived detection proves it invertible. This follows the seven proof steps of the node. -/
theorem isIso_comparisonDirectImagePlus (Λ : Type (u + 1)) [Ring Λ]
    {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)
  exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)))
    (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
      (ModuleCat.{u + 1} Λ) f I)

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonRestriction_id (Λ : Type (u + 1)) [Ring Λ]
    (U : Scheme.{u}) (G : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    (lowerStarCompComparisonLowerStarIso (𝟙 U) (ModuleCat.{u + 1} Λ)).inv.app G ≫
        (comparisonLowerStar (ModuleCat.{u + 1} Λ) U).map
          ((lowerStarId (ModuleCat.{u + 1} Λ) U).hom.app G) =
      (Etale.lowerStarId (ModuleCat.{u + 1} Λ) U).hom.app
        ((comparisonLowerStar (ModuleCat.{u + 1} Λ) U).obj G) := by
  apply (sheafToPresheaf _ _).map_injective
  refine NatTrans.ext (funext fun W ↦ ?_)
  dsimp only [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso,
    lowerStarId, Etale.lowerStarId, GrothendieckTopology.lowerStarId, comparisonLowerStar,
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousId']
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, Iso.refl_symm,
    Iso.trans_inv, Iso.refl_inv, Category.assoc, NatTrans.comp_app, NatTrans.id_app,
    Iso.trans_hom, Functor.map_comp, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    Functor.sheafPushforwardContinuous_map_hom, Functor.whiskerRight_app,
    Functor.op_obj, NatTrans.op_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
    CategoryTheory.op_id, Functor.whiskerLeft_app,
    Functor.sheafPushforwardContinuousId_hom_app_hom_app, Opposite.op_unop,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op]
  change 𝟙 _ ≫ G.obj.map (𝟙 _) ≫ 𝟙 _ ≫ G.obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app
        ((Scheme.toProEt U).obj (Opposite.unop W))).op ≫ 𝟙 _ =
    G.obj.map ((Scheme.toProEt U).map
      ((MorphismProperty.Over.pullbackId @Etale ⊤ U).inv.app (Opposite.unop W))).op ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rw [G.obj.map_id, Category.id_comp]
  rfl

private theorem comparisonUnderived_id (Λ : Type (u + 1)) [Ring Λ]
    (U : Scheme.{u}) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (lowerStarComparisonUpperStarBaseChange (𝟙 U) (ModuleCat.{u + 1} Λ)).app F ≫
        (lowerStarId (ModuleCat.{u + 1} Λ) U).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
        ((Etale.lowerStarId (ModuleCat.{u + 1} Λ) U).hom.app F) := by
  apply ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := unit_mateEquiv_symm
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (lowerStarCompComparisonLowerStarIso (𝟙 U) (ModuleCat.{u + 1} Λ)).inv F
  simp only [Functor.id_obj] at h
  dsimp only [lowerStarComparisonUpperStarBaseChange]
  rw [← Category.assoc, ← h]
  rw [Category.assoc, comparisonRestriction_id]
  exact ((Etale.lowerStarId (ModuleCat.{u + 1} Λ) U).hom.naturality
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).unit.app F)).trans
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).unit.naturality _)

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonRestriction_comp (Λ : Type (u + 1)) [Ring Λ]
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (G : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv.app G) ≫
      (lowerStarCompComparisonLowerStarIso g (ModuleCat.{u + 1} Λ)).inv.app
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
      (comparisonLowerStar (ModuleCat.{u + 1} Λ) W).map
        ((lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app G) =
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app
        ((comparisonLowerStar (ModuleCat.{u + 1} Λ) U).obj G) ≫
      (lowerStarCompComparisonLowerStarIso (f ≫ g) (ModuleCat.{u + 1} Λ)).inv.app G := by
  apply (sheafToPresheaf _ _).map_injective
  refine NatTrans.ext (funext fun T ↦ ?_)
  dsimp only [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso,
    lowerStar, Etale.lowerStar, GrothendieckTopology.lowerStar,
    lowerStarComp, Etale.lowerStarComp, GrothendieckTopology.lowerStarComp,
    comparisonLowerStar, Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_inv, Iso.refl_inv, NatTrans.comp_app, NatTrans.id_app, Functor.map_comp,
    Iso.symm_inv, Iso.symm_hom, Category.assoc, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuous_map_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerLeft_app, Functor.op_obj,
    Functor.whiskerRight_app, NatTrans.op_app, NatIso.ofComponents_hom_app,
    Iso.refl_hom, CategoryTheory.op_id,
    Functor.sheafPushforwardContinuous_obj_obj_map, CategoryTheory.unop_id_op,
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map_id, Quiver.Hom.unop_op]
  change 𝟙 _ ≫ G.obj.map (𝟙 _) ≫ 𝟙 _ ≫ G.obj.map (𝟙 _) ≫ G.obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app
        ((Scheme.toProEt W).obj (Opposite.unop T))).op =
    G.obj.map ((Scheme.toProEt U).map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).hom.app
        (Opposite.unop T))).op ≫ 𝟙 _ ≫ G.obj.map (𝟙 _)
  rw [G.obj.map_id, G.obj.map_id]
  simp only [Category.id_comp, Category.comp_id]
  rfl

private theorem mate_comp {A B C A' B' C' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    {N : A ⥤ A'} {NR : A' ⥤ A} {M : B ⥤ B'} {MR : B' ⥤ B}
    {T : C ⥤ C'} {TR : C' ⥤ C}
    (aN : N ⊣ NR) (aM : M ⊣ MR) (aT : T ⊣ TR)
    {E : A ⥤ B} {H : B ⥤ C} {EH : A ⥤ C}
    {P : A' ⥤ B'} {Q : B' ⥤ C'} {PQ : A' ⥤ C'}
    (e : E ⋙ H ≅ EH) (e' : P ⋙ Q ≅ PQ)
    (r : P ⋙ MR ≅ NR ⋙ E) (s : Q ⋙ TR ≅ MR ⋙ H)
    (t : PQ ⋙ TR ≅ NR ⋙ EH)
    (hr : ∀ G, H.map (r.inv.app G) ≫ s.inv.app (P.obj G) ≫ TR.map (e'.hom.app G) =
      e.hom.app (NR.obj G) ≫ t.inv.app G) (F : A) :
    T.map (e.hom.app F) ≫ ((mateEquiv aN aT).symm t.inv).app F =
      ((mateEquiv aM aT).symm s.inv).app (E.obj F) ≫
        Q.map (((mateEquiv aN aM).symm r.inv).app F) ≫ e'.hom.app (N.obj F) := by
  have hf := unit_mateEquiv_symm aN aM r.inv F
  have hg := unit_mateEquiv_symm aM aT s.inv (E.obj F)
  have hfg := unit_mateEquiv_symm aN aT t.inv F
  simp only [Functor.id_obj] at hf hg hfg
  apply (aT.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := aT.unit.naturality (e.hom.app F)
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [← reassoc_of% hn, ← hfg]
  have he := e.hom.naturality (aN.unit.app F)
  simp only [Functor.comp_map, Functor.comp_obj] at he
  erw [← reassoc_of% he, ← reassoc_of% hg]
  have hs := s.inv.naturality (((mateEquiv aN aM).symm r.inv).app F)
  simp only [Functor.comp_map, Functor.comp_obj] at hs
  erw [← reassoc_of% hs, ← H.map_comp_assoc, ← hf, H.map_comp, Category.assoc, hr]

private theorem comparisonUnderived_comp (Λ : Type (u + 1)) [Ring Λ]
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
        ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F) ≫
      (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} Λ)).app F =
    (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ)).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F)  := by
  simpa only [lowerStarComparisonUpperStarBaseChange] using mate_comp
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) W)
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f g)
    (lowerStarComp (ModuleCat.{u + 1} Λ) f g)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ))
    (lowerStarCompComparisonLowerStarIso g (ModuleCat.{u + 1} Λ))
    (lowerStarCompComparisonLowerStarIso (f ≫ g) (ModuleCat.{u + 1} Λ))
    (comparisonRestriction_comp Λ f g) F

private theorem mapHT_whiskerRight {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (H : D ⥤ E) [H.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight α H)).app K =
      H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus α).app K) := rfl

private theorem mapHT_whiskerLeft {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) [F.Additive] {G H : D ⥤ E} [G.Additive] [H.Additive]
    (α : G ⟶ H) (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft F α)).app K =
      (NatTrans.mapHomotopyCategoryPlus α).app (F.mapHomotopyCategoryPlus.obj K) := rfl

private theorem derivedId_fac {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] (F : C ⥤ C) [F.Additive]
    (e : F ≅ 𝟭 C) (K : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (Functor.rightDerivedFunctorPlusNatIso e ≪≫
          Functor.rightDerivedFunctorPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  change F.rightDerivedFunctorPlusUnith.app K ≫
    (Functor.rightDerivedFunctorPlusNatTrans e.hom).app _ ≫ _ = _
  rw [← Category.assoc, Functor.rightDerivedFunctorPlusNatTrans_app, Category.assoc,
    Functor.rightDerivedFunctorPlusIdIso_fac_app,
    Functor.mapHomotopyCategoryPlusIdIso_hom_app_eq_id,
    DerivedCategory.Plus.Qh.map_id K]
  erw [Category.comp_id]

private theorem derivedBaseChange_fac {B B' C C' : Type*}
    [Category* B] [Category* B'] [Category* C] [Category* C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
    [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
    [Limits.PreservesFiniteLimits β] [Limits.PreservesFiniteColimits β]
    [Limits.PreservesFiniteLimits γ] [Limits.PreservesFiniteColimits γ]
    (e : G ⋙ γ ⟶ β ⋙ G') (K : HomotopyCategory.Plus B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnith.app K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Qh.obj K) =
      γ.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
        G'.rightDerivedFunctorPlusUnith.app (β.mapHomotopyCategoryPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have h := NatTrans.congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e) K
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Category.id_comp,
    Category.comp_id] at h
  erw [DerivedCategory.Plus.Qh.map_id, DerivedCategory.Plus.Qh.map_id] at h
  erw [Category.id_comp, Category.id_comp] at h
  exact h

private theorem derived_identity {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [EnoughInjectives D]
    (E : C ⥤ C) (P : D ⥤ D) (N : C ⥤ D)
    [E.Additive] [P.Additive] [N.Additive]
    [Limits.PreservesFiniteLimits N] [Limits.PreservesFiniteColimits N]
    (eE : E ≅ 𝟭 C) (eP : P ≅ 𝟭 D) (b : E ⋙ N ⟶ N ⋙ P)
    (hb : ∀ F, b.app F ≫ eP.hom.app (N.obj F) = N.map (eE.hom.app F))
    (L : DerivedCategory.Plus C) :
    (Functor.rightDerivedFunctorPlusBaseChange b).app L ≫
      (Functor.rightDerivedFunctorPlusNatIso eP ≪≫
        Functor.rightDerivedFunctorPlusIdIso D).hom.app (N.mapDerivedCategoryPlus.obj L) =
    N.mapDerivedCategoryPlus.map ((Functor.rightDerivedFunctorPlusNatIso eE ≪≫
      Functor.rightDerivedFunctorPlusIdIso C).hom.app L) := by
  let dE := Functor.rightDerivedFunctorPlusNatIso eE ≪≫ Functor.rightDerivedFunctorPlusIdIso C
  let dP := Functor.rightDerivedFunctorPlusNatIso eP ≪≫ Functor.rightDerivedFunctorPlusIdIso D
  have h : Functor.rightDerivedFunctorPlusBaseChange b ≫
      Functor.whiskerLeft N.mapDerivedCategoryPlus dP.hom ≫
      N.mapDerivedCategoryPlus.rightUnitor.hom =
    Functor.whiskerRight dE.hom N.mapDerivedCategoryPlus ≫
      N.mapDerivedCategoryPlus.leftUnitor.hom := by
    apply Functor.rightDerived_ext (E.rightDerivedFunctorPlus ⋙ N.mapDerivedCategoryPlus)
      (Functor.whiskerRight E.rightDerivedFunctorPlusUnith N.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso _)
    ext K : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_hom_app, Category.comp_id]
    rw [← Category.assoc, derivedBaseChange_fac]
    have hn := dP.hom.naturality (N.mapDerivedCategoryPlusFactorsh.inv.app K)
    simp only [Functor.comp_obj, Functor.id_map] at hn
    erw [Category.comp_id, Category.comp_id]
    simp only [Category.assoc]
    erw [hn]
    have hf := derivedId_fac P eP
      (N.mapHomotopyCategoryPlus.obj K)
    erw [reassoc_of% hf]
    rw [← DerivedCategory.Plus.Qh.map_comp_assoc]
    have hu : (NatTrans.mapHomotopyCategoryPlus b).app K ≫
        (NatTrans.mapHomotopyCategoryPlus
          eP.hom).app
            (N.mapHomotopyCategoryPlus.obj K) =
      N.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus
        eE.hom).app K) := by
      have h₀ : b ≫ Functor.whiskerLeft N
          eP.hom =
        Functor.whiskerRight eE.hom N := by
        ext F : 2
        exact hb F
      have h₁ := NatTrans.congr_app
        (congrArg NatTrans.mapHomotopyCategoryPlus h₀) K
      simpa only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
        mapHT_whiskerRight, mapHT_whiskerLeft] using h₁
    rw [hu]
    have hn' := N.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus
        eE.hom).app K)
    simp only [Functor.comp_map, Functor.comp_obj] at hn'
    rw [← reassoc_of% hn']
    erw [N.mapDerivedCategoryPlusFactorsh.hom_inv_id_app K, Category.comp_id]
    rw [← N.mapDerivedCategoryPlus.map_comp, derivedId_fac]
  have hL := NatTrans.congr_app h L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hL
  erw [Category.comp_id, Category.comp_id] at hL
  exact hL

/-- Identity compatibility of the canonical derived comparison.
Source: blueprint theorem-comparison-direct-images--1, final proof paragraph
(blueprint: theorem-comparison-direct-images--1).

Proof: for the identity morphism the defining pulled-back counit mate is the identity
under the canonical identity identifications. The adjunction triangle identities cancel
the inserted unit and counit. Deriving preserves this equality by the universal property
of the bounded below right derived functor and its normalization on injective complexes. -/
theorem comparisonDirectImagePlus_id (Λ : Type (u + 1)) [Ring Λ]
    (U : Scheme.{u})
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange (𝟙 U) (ModuleCat.{u + 1} Λ))).app L ≫
      (Functor.rightDerivedFunctorPlusNatIso
        (lowerStarId (ModuleCat.{u + 1} Λ) U) ≪≫
          Functor.rightDerivedFunctorPlusIdIso _).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj L) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
      ((Functor.rightDerivedFunctorPlusNatIso
        (Etale.lowerStarId (ModuleCat.{u + 1} Λ) U) ≪≫
          Functor.rightDerivedFunctorPlusIdIso _).hom.app L) := by
  exact derived_identity _ _ _
    (Etale.lowerStarId (ModuleCat.{u + 1} Λ) U)
    (lowerStarId (ModuleCat.{u + 1} Λ) U)
    (lowerStarComparisonUpperStarBaseChange (𝟙 U) (ModuleCat.{u + 1} Λ))
    (comparisonUnderived_id Λ U) L

private theorem derived_comp
    {C D E C' D' E' : Type*}
    [Category* C] [Category* D] [Category* E]
    [Category* C'] [Category* D'] [Category* E']
    [Abelian C] [Abelian D] [Abelian E] [Abelian C'] [Abelian D'] [Abelian E']
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory C'] [HasDerivedCategory D'] [HasDerivedCategory E']
    [EnoughInjectives C] [EnoughInjectives D]
    [EnoughInjectives C'] [EnoughInjectives D']
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (F' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E')
    (β : C ⥤ C') (γ : D ⥤ D') (δ : E ⥤ E')
    [F.Additive] [G.Additive] [H.Additive] [F'.Additive] [G'.Additive] [H'.Additive]
    [β.Additive] [γ.Additive] [δ.Additive]
    [Limits.PreservesFiniteLimits β] [Limits.PreservesFiniteColimits β]
    [Limits.PreservesFiniteLimits γ] [Limits.PreservesFiniteColimits γ]
    [Limits.PreservesFiniteLimits δ] [Limits.PreservesFiniteColimits δ]
    [F.PreservesInjectiveObjects] [F'.PreservesInjectiveObjects]
    (c : F ⋙ G ≅ H) (c' : F' ⋙ G' ≅ H')
    (eF : F ⋙ γ ⟶ β ⋙ F') (eG : G ⋙ δ ⟶ γ ⋙ G') (eH : H ⋙ δ ⟶ β ⋙ H')
    (he : eH = Functor.whiskerRight c.inv δ ≫ Functor.whiskerLeft F eG ≫
      Functor.whiskerRight eF G' ≫ Functor.whiskerLeft β c'.hom)
    (L : DerivedCategory.Plus C) :
    δ.mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' F G c).hom.app L) ≫
      (Functor.rightDerivedFunctorPlusBaseChange eH).app L =
    (Functor.rightDerivedFunctorPlusBaseChange eG).app (F.rightDerivedFunctorPlus.obj L) ≫
      G'.rightDerivedFunctorPlus.map ((Functor.rightDerivedFunctorPlusBaseChange eF).app L) ≫
      (Functor.rightDerivedFunctorPlusCompIso' F' G' c').hom.app
        (β.mapDerivedCategoryPlus.obj L) := by
  let d := Functor.rightDerivedFunctorPlusCompIso' F G c
  let d' := Functor.rightDerivedFunctorPlusCompIso' F' G' c'
  have h : Functor.rightDerivedFunctorPlusBaseChange eH =
      Functor.whiskerRight d.inv δ.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus
          (Functor.rightDerivedFunctorPlusBaseChange eG) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.rightDerivedFunctorPlusBaseChange eF)
          G'.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft β.mapDerivedCategoryPlus d'.hom := by
    symm
    apply Functor.rightDerived_ext (H.rightDerivedFunctorPlus ⋙ δ.mapDerivedCategoryPlus)
      (Functor.whiskerRight H.rightDerivedFunctorPlusUnith δ.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso _)
    ext K : 2
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
      Category.id_comp, Category.comp_id]
    have hCI1 : H.rightDerivedFunctorPlusUnith.app K ≫
        d.inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K) ≫
        G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) := by
      have hc := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac F G c) K
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.comp_obj, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at hc
      have hc' : H.rightDerivedFunctorPlusUnith.app K =
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K) ≫
            G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
            G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
            d.hom.app (DerivedCategory.Plus.Qh.obj K) := by
        erw [hc, ← Category.assoc, ← DerivedCategory.Plus.Qh.map_comp,
          ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
          NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
          DerivedCategory.Plus.Qh.map_id, Category.id_comp]
      rw [hc']
      simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
    have hnat₂ := (Functor.rightDerivedFunctorPlusBaseChange eG).naturality
      (F.rightDerivedFunctorPlusUnith.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hnat₂
    have hfac₂ := derivedBaseChange_fac eG (F.mapHomotopyCategoryPlus.obj K)
    have hfac₁ := derivedBaseChange_fac eF K
    have hnatη : DerivedCategory.Plus.Qh.map
        (G'.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus eF).app K)) ≫
          G'.rightDerivedFunctorPlusUnith.app
            (F'.mapHomotopyCategoryPlus.obj (β.mapHomotopyCategoryPlus.obj K)) =
        G'.rightDerivedFunctorPlusUnith.app
            (γ.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
          G'.rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus eF).app K)) :=
      G'.rightDerivedFunctorPlusUnith.naturality _
    have hCI2 := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac F' G' c')
      (β.mapHomotopyCategoryPlus.obj K)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at hCI2
    have hnatCI := d'.hom.naturality (β.mapDerivedCategoryPlusFactorsh.inv.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hnatCI
    have hnatδ : δ.mapDerivedCategoryPlus.map
        (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K)) ≫
          δ.mapDerivedCategoryPlusFactorsh.hom.app
            (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) =
        δ.mapDerivedCategoryPlusFactorsh.hom.app (H.mapHomotopyCategoryPlus.obj K) ≫
          DerivedCategory.Plus.Qh.map (δ.mapHomotopyCategoryPlus.map
            ((NatTrans.mapHomotopyCategoryPlus c.inv).app K)) :=
      δ.mapDerivedCategoryPlusFactorsh.hom.naturality _
    have hpaste : (NatTrans.mapHomotopyCategoryPlus eH).app K =
        δ.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app K) ≫
          (NatTrans.mapHomotopyCategoryPlus eG).app (F.mapHomotopyCategoryPlus.obj K) ≫
          G'.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus eF).app K) ≫
          (NatTrans.mapHomotopyCategoryPlus c'.hom).app
            (β.mapHomotopyCategoryPlus.obj K) := by
      rw [he]
      simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
        mapHT_whiskerRight, mapHT_whiskerLeft]
    rw [← Functor.map_comp_assoc, hCI1, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc, reassoc_of% hnat₂, reassoc_of% hfac₂, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, Category.assoc, hfac₁, Iso.inv_hom_id_app_assoc,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      ← reassoc_of% hnatη, hnatCI, reassoc_of% hCI2, reassoc_of% hnatδ]
    rw [derivedBaseChange_fac, hpaste, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
  have hL := NatTrans.congr_app h L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hL
  rw [hL]
  rw [← Category.assoc, ← δ.mapDerivedCategoryPlus.map_comp, Iso.hom_inv_id_app,
    δ.mapDerivedCategoryPlus.map_id, Category.id_comp]

/-- Composition compatibility of the canonical derived comparison.
Source: blueprint theorem-comparison-direct-images--1, final proof paragraph
(blueprint: theorem-comparison-direct-images--1).

Proof: the counit of a composite adjunction is the composite of its two counits under
associativity. Substitute this into the defining mate formula. Pullback comparison
coherence identifies the two pullback paths, and the triangle identities cancel the
inserted unit-counit pairs. On bounded below injective representatives, direct images
preserve injectives because inverse images are exact. Thus the canonical derived
composition isomorphisms compute the same equality termwise; their universal-property
normalizations give the displayed formula. Naturality in L is already the naturality
of the derived base-change transformation. -/
theorem comparisonDirectImagePlus_comp (Λ : Type (u + 1)) [Ring Λ]
    {U V W : Scheme.{u}}
    (f : U ⟶ V) (g : V ⟶ W)
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategoryPlus.map
      ((etaleComparisonDirectImageCompIso Λ f g).hom.app L) ≫
      (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} Λ))).app L =
    (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ))).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))).app L) ≫
      (proEtaleComparisonDirectImageCompIso Λ f g).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj L) := by
  let A := ModuleCat.{u + 1} Λ
  let F := Etale.lowerStar A f
  let G := Etale.lowerStar A g
  let H := Etale.lowerStar A (f ≫ g)
  let F' := lowerStar A f
  let G' := lowerStar A g
  let H' := lowerStar A (f ≫ g)
  let N := comparisonUpperStar A U
  let M := comparisonUpperStar A V
  let T := comparisonUpperStar A W
  let c := Etale.lowerStarComp A f g
  let c' := lowerStarComp A f g
  let eF := lowerStarComparisonUpperStarBaseChange f A
  let eG := lowerStarComparisonUpperStarBaseChange g A
  let eH := lowerStarComparisonUpperStarBaseChange (f ≫ g) A
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction A f)
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction A f)
  have he : eH = Functor.whiskerRight c.inv T ≫ Functor.whiskerLeft F eG ≫
      Functor.whiskerRight eF G' ≫ Functor.whiskerLeft N c'.hom := by
    ext K : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply (cancel_epi (T.map (c.hom.app K))).mp
    rw [← T.map_comp_assoc, Iso.hom_inv_id_app, T.map_id, Category.id_comp]
    exact comparisonUnderived_comp Λ f g K
  exact derived_comp F G H F' G' H' N M T c c' eF eG eH he L

end AlgebraicGeometry.ProEtale
