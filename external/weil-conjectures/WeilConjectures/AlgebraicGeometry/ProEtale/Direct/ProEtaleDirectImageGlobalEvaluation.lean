/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleUnitLerayChainFormula
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackIdentity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleUnitLerayChainFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleComparisonLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

/-!
# Normalized derived global sections after ordinary pro-etale direct image

The section functor and its terminal-object comparison are the ordinary
constant-ring constructions. All derived images below are the actual finite-level
sectionwise direct image, without completion or a constructibility restriction.

## References

* Stacks Project, Tags 0D6H and 0D6E
* Tags 070Y and 0DVC
* Stacks Tag 07A5
-/

@[expose] public noncomputable section
set_option autoImplicit false
section
attribute [-instance]
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- Fix abelian-group sheafification at the coefficient universe. -/
private noncomputable local instance (priority := 5000) globalEvaluation_sheafify
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

/-- Use the locally-bijective characterization at that same universe. -/
private noncomputable local instance (priority := 5000) globalEvaluation_locallyBijective
    (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

/-- Finiteness of the conventions' coefficient ring, supplied by its quotient
construction. -/
instance purityGlobalEvaluation_finiteRing (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Ring :=
  WeilConjectures.PurityFiniteSetting.ringFinite.{u} P

/-- The terminal-object comparison, written for the actual finite direct image. -/
def proEtaleGlobalEvaluationTerminal (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantModuleDirectImage f A ⋙ proEtaleUnitLeraySections A Y ≅
      proEtaleUnitLeraySections A X :=
  isoWhiskerRight (proEtaleUnitLerayDirectImageIso A f).symm
    (proEtaleUnitLeraySections A Y) ≪≫ proEtaleUnitLerayTerminalIso A f

/-- The normalized identity inverse image. The source theorem specifies every section
of its module comparison, its termwise extension, and its localization, so the extracted
isomorphism is determined by that normalization rather than by bare existence. -/
def proEtaleGlobalEvaluationPullbackId (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) : proEtaleConstantRingDerivedPullback A (𝟙 X) ≅ 𝟭 _ :=
  (proEtaleDerivedPullback_identity X A).choose_spec.2.2.choose_spec.2.choose_spec.2.2
    |>.choose_spec.2.choose

section MateTransport
variable {C D E : Type*} [Category C] [Category D] [Category E]
  {Lf : D ⥤ C} {Lg : E ⥤ D} {Lc : E ⥤ C}
  {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
  (af : Lf ⊣ F) (ag : Lg ⊣ G) (ac : Lc ⊣ H)
  (ef : F ≅ F') (eg : G ≅ G') (ec : H ≅ H')
  (a : Lc ⟶ Lg ⋙ Lf)
private theorem mateTransport :
    conjugateEquiv ((ag.ofNatIsoRight eg).comp (af.ofNatIsoRight ef))
      (ac.ofNatIsoRight ec) a =
      Functor.whiskerRight ef.inv G' ≫ Functor.whiskerLeft F eg.inv ≫
        conjugateEquiv (ag.comp af) ac a ≫ ec.hom := by
  have hc (M : C) :
      ((ag.ofNatIsoRight eg).comp (af.ofNatIsoRight ef)).counit.app M =
        (Lg ⋙ Lf).map (G'.map (ef.inv.app M) ≫ eg.inv.app (F.obj M)) ≫
          (ag.comp af).counit.app M := by
    simp only [Adjunction.comp_counit_app, Adjunction.ofNatIsoRight_counit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.map_comp, Category.assoc]
    have hn := ag.counit.naturality (ef.inv.app M)
    have he := eg.inv.naturality (ef.inv.app M)
    simp only [Functor.comp_map, Functor.id_map] at hn he
    rw [← Lf.map_comp_assoc (ag.counit.app _) (ef.inv.app M), ← hn]
    simpa only [Lf.map_comp, Lg.map_comp, Category.assoc] using
      (congrArg (fun t ↦ Lf.map (Lg.map t) ≫
        Lf.map (ag.counit.app (F.obj M)) ≫ af.counit.app M) he).symm
  apply NatTrans.ext
  funext M
  let t := G'.map (ef.inv.app M) ≫ eg.inv.app (F.obj M)
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [hc, ← H'.map_comp]
  rw [← ec.hom.naturality]
  rw [H.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc]
  erw [← a.naturality t]
  rw [H.map_comp, Category.assoc]
  erw [← ac.unit.naturality_assoc t]
  simp only [t, Functor.comp_obj, Functor.id_map, Category.assoc]

end MateTransport

private lemma comp_unit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  dsimp
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedComp
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions B]
    (F : C ⥤ D) (G : D ⥤ B) (H : B ⥤ E) (K : C ⥤ B) (J : D ⥤ E) (L : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] [J.Additive] [L.Additive]
    [F.PreservesKInjectiveComplexes] [G.PreservesKInjectiveComplexes]
    [K.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ K) (a : G ⋙ H ≅ J) (b : F ⋙ J ≅ L) (c : K ⋙ H ≅ L)
    (he : ∀ M : C, H.map (e.hom.app M) ≫ c.hom.app M =
      a.hom.app (F.obj M) ≫ b.hom.app M) :
    Functor.whiskerRight (Functor.rightDerivedFunctorCompIso' F G e).hom
        H.rightDerivedFunctor ≫ (Functor.rightDerivedFunctorCompIso' K H c).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctor (Functor.rightDerivedFunctorCompIso' G H a).hom ≫
        (Functor.rightDerivedFunctorCompIso' F J b).hom := by
  let d := Functor.rightDerivedFunctorCompIso' F G e
  have : (F ⋙ G).PreservesKInjectiveComplexes := ⟨fun T _ => by
    change CochainComplex.IsKInjective
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T))
    infer_instance⟩
  let i := Functor.isoWhiskerRight (Functor.rightDerivedFunctorCompIso F G)
    H.rightDerivedFunctor
  let α := Functor.rightDerivedFunctorCompUnit (F ⋙ G) H ≫
    Functor.whiskerLeft DerivedCategory.Qh i.hom
  have : ((F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) ⋙ H.rightDerivedFunctor
      ).IsRightDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (Functor.isRightDerivedFunctor_iff_of_iso
      (Functor.rightDerivedFunctorCompUnit (F ⋙ G) H) α
      (HomotopyCategory.quasiIso _ (.up ℤ)) i rfl).mp inferInstance
  refine Functor.rightDerived_ext _ α (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext T : 2
  have hα : α.app T =
      H.rightDerivedFunctorUnit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj T)) ≫
        H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) := by
    dsimp only [α, i, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    rw [comp_unit_app]
    erw [Category.assoc, ← Functor.map_comp]
    congr 2
    simp [Functor.rightDerivedFunctorCompIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, hα, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [Category.id_comp]
  have hfg := NatTrans.congr_app (unitLerayFac e) T
  have hc := NatTrans.congr_app (unitLerayFac c) T
  have ha := NatTrans.congr_app (unitLerayFac a)
    ((F.mapHomotopyCategory (.up ℤ)).obj T)
  have hb := NatTrans.congr_app (unitLerayFac b) T
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hfg hc ha hb
  rw [comp_unit_app] at hc ha hb
  have hn := H.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app T)
  have hna := (Functor.rightDerivedFunctorCompIso' G H a).hom.naturality
    (F.rightDerivedFunctorUnit.app T)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hna
  change H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      H.rightDerivedFunctor.map (d.hom.app (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' K H c).hom.app (DerivedCategory.Qh.obj T) =
    H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      (Functor.rightDerivedFunctorCompIso' G H a).hom.app
        (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' F J b).hom.app (DerivedCategory.Qh.obj T)
  rw [← Functor.map_comp_assoc, hfg, Functor.map_comp]
  simp only [Category.assoc] at hc ha hb ⊢
  erw [← reassoc_of% hn]
  erw [hc]
  rw [comp_unit_app, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hna, reassoc_of% ha, hb]
  rw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
  have ht : (H.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app T) ≫
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app T =
    (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj T) ≫
      (NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app T := by
    ext n : 1
    exact he (T.X n)
  have hq := (HomotopyCategory.quotient E (.up ℤ)).congr_map ht
  simp only [NatTrans.mapHomotopyCategory_app,
    HomotopyCategory.quotient_obj_as, Functor.mapHomotopyCategory_map,
    Functor.map_comp] at hq ⊢
  exact hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedIdentity
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions C]
    (L F : C ⥤ C) (G : C ⥤ E) [L.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [F.PreservesKInjectiveComplexes]
    (a : L ⊣ F) (e : F ⋙ G ≅ G) (α : L ≅ 𝟭 C)
    (β : L.mapDerivedCategory ≅ 𝟭 (DerivedCategory C))
    (hβ : ∀ I : CochainComplex C ℤ,
      β.hom.app (DerivedCategory.Q.obj I) = L.mapDerivedCategoryFactors.hom.app I ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I))
    (h : whiskerRight a.unit G ≫ whiskerLeft L e.hom ≫ whiskerRight α.hom G = 𝟙 G) :
    (Functor.rightDerivedFunctorCompIso' F G e).hom =
      whiskerRight (conjugateIsoEquiv a.mapDerivedCategoryRightDerivedAdjunction
        Adjunction.id β.symm).hom G.rightDerivedFunctor := by
  let d := conjugateIsoEquiv a.mapDerivedCategoryRightDerivedAdjunction Adjunction.id β.symm
  have hd (K : DerivedCategory C) : d.inv.app K =
      a.mapDerivedCategoryRightDerivedAdjunction.unit.app K ≫
        F.rightDerivedFunctor.map (β.hom.app K) := by
    simpa only [d, conjugateIsoEquiv_apply_inv, Iso.symm_inv, Adjunction.id_unit,
      NatTrans.id_app, Category.id_comp, Functor.id_obj] using
        unit_conjugateEquiv Adjunction.id a.mapDerivedCategoryRightDerivedAdjunction β.hom K
  apply NatTrans.ext
  funext K
  obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have heq : (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Q.obj I) =
      G.rightDerivedFunctor.map (d.hom.app (DerivedCategory.Q.obj I)) := by
    have hc := unitLerayChain a e I I ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I)
    rw [← hβ] at hc
    have hn := (Functor.rightDerivedFunctorCompIso' F G e).hom.naturality
      (β.hom.app (DerivedCategory.Q.obj I))
    dsimp only [Functor.comp_map] at hn
    erw [← hn, ← G.rightDerivedFunctor.map_comp_assoc, ← hd] at hc
    have hh : (NatTrans.mapHomologicalComplex
        (whiskerRight a.unit G ≫ whiskerLeft L e.hom) (.up ℤ)).app I ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) = 𝟙 _ := by
      ext n : 1
      change (G.map (a.unit.app (I.X n)) ≫ e.hom.app (L.obj (I.X n))) ≫
        G.map (α.hom.app (I.X n)) = 𝟙 _
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
        Functor.mapHomologicalComplex_obj_X,
        Functor.comp_obj, Functor.id_obj,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatTrans.id_app, Category.assoc] using congr_app h (I.X n)
    erw [hh, DerivedCategory.Q.map_id, Category.id_comp, Iso.hom_inv_id] at hc
    apply (cancel_epi (G.rightDerivedFunctor.map (d.inv.app _))).mp
    rw [← G.rightDerivedFunctor.map_comp, d.inv_hom_id_app,
      G.rightDerivedFunctor.map_id]
    exact hc.symm
  apply (cancel_epi ((F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).map i.inv)).mp
  rw [(Functor.rightDerivedFunctorCompIso' F G e).hom.naturality, heq]
  simp only [Functor.whiskerRight_app, Functor.comp_map]
  rw [← G.rightDerivedFunctor.map_comp, ← G.rightDerivedFunctor.map_comp]
  exact G.rightDerivedFunctor.congr_map (d.hom.naturality i.inv).symm

attribute [local irreducible] proEtaleUnitLerayDirectImageIso

section SectionRealization
variable (A : Type u) [CommRing A] [Finite A]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnit_bijective (X : Scheme.{u})
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : X.ProEtᵒᵖ) :
    Function.Bijective (sfIntrinsicRealizationUnit X A M W) := by
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap X A
  let N := (ProEtale.finiteCoefficientModulePresheaf X.ProEt
    (ULift.{u + 1, u} A)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app N
  have : IsIso η := by
    dsimp only [η, α, N]
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj
        M).property
  have : IsIso (η.app W) := inferInstanceAs
    (IsIso ((PresheafOfModules.evaluation _ W).map η))
  exact ConcreteCategory.bijective_of_isIso (η.app W)

private def sectionRealization (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : X.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.obj W) : M.val.obj W :=
  ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W
    (sfIntrinsicRealizationUnit X A ((sfIntrinsicModuleEquivalence X A).inverse.obj M) W m)

set_option backward.isDefEq.respectTransparency false in
private theorem sectionRealization_bijective (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : X.ProEtᵒᵖ) :
    Function.Bijective (sectionRealization A X M W) := by
  have : IsIso (((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ W).map
      ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M)))
  exact (ConcreteCategory.bijective_of_isIso
    (((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W)).comp
      (scalarUnit_bijective A X _ W)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnit_naturality (X : Scheme.{u})
    {M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (W : X.ProEtᵒᵖ) (m : M.obj.obj W) :
    sfIntrinsicRealizationUnit X A N W (f.hom.app W m) =
      (((sfIntrinsicModuleEquivalence X A).functor.map f).val.app W)
        (sfIntrinsicRealizationUnit X A M W m) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun h ↦ h.app W)
      ((PresheafOfModules.sheafificationAdjunction
        (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.naturality
          ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
            (ULift.{u + 1, u} A)).map f.hom))) m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionRealization_naturality (X : Scheme.{u})
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (f : M ⟶ N) (W : X.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.obj W) :
    sectionRealization A X N W
        (((sfIntrinsicModuleEquivalence X A).inverse.map f).hom.app W m) =
      f.val.app W (sectionRealization A X M W m) := by
  unfold sectionRealization
  rw [scalarUnit_naturality]
  exact ConcreteCategory.congr_hom
    (congrArg (fun h ↦ h.val.app W)
      ((sfIntrinsicModuleEquivalence X A).counitIso.hom.naturality f)) _
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionRealization_functor (X : Scheme.{u})
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : X.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj M)).obj.obj W) :
    sectionRealization A X ((sfIntrinsicModuleEquivalence X A).functor.obj M) W m =
      sfIntrinsicRealizationUnit X A M W
        (((sfIntrinsicModuleEquivalence X A).unitIso.inv.app M).hom.app W m) := by
  unfold sectionRealization
  have he := (sfIntrinsicModuleEquivalence X A).counit_app_functor M
  change (sfIntrinsicModuleEquivalence X A).counitIso.hom.app
      ((sfIntrinsicModuleEquivalence X A).functor.obj M) = _ at he
  rw [he]
  exact (scalarUnit_naturality A X
    ((sfIntrinsicModuleEquivalence X A).unitIso.inv.app M) W m).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionRealization_restrict (X : Scheme.{u})
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    {V W : X.ProEtᵒᵖ} (f : V ⟶ W)
    (m : ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.obj V) :
    sectionRealization A X M W
        (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map f m) =
      M.val.map f (sectionRealization A X M V m) := by
  unfold sectionRealization
  have hu : sfIntrinsicRealizationUnit X A
      ((sfIntrinsicModuleEquivalence X A).inverse.obj M) W
      (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map f m) =
      (((sfIntrinsicModuleEquivalence X A).functor.obj
        ((sfIntrinsicModuleEquivalence X A).inverse.obj M)).val.map f)
        (sfIntrinsicRealizationUnit X A
          ((sfIntrinsicModuleEquivalence X A).inverse.obj M) V m) :=
    PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction
        (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.app
        ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
          (ULift.{u + 1, u} A)).obj ((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj)) f m
  exact (congrArg (fun x ↦
    ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app W x) hu).trans
      (PresheafOfModules.naturality_apply
        ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val f _)

private def sectionDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantModuleDirectImage f A ⋙ (sfIntrinsicModuleEquivalence Y A).inverse ≅
      (sfIntrinsicModuleEquivalence X A).inverse ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f :=
  isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso.symm
      (proEtaleConstantModuleDirectImage f A ⋙ (sfIntrinsicModuleEquivalence Y A).inverse) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (isoWhiskerRight (sfIntrinsicDirectImageComparison f A)
        (sfIntrinsicModuleEquivalence Y A).inverse) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (Functor.associator
          (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
          (sfIntrinsicModuleEquivalence Y A).functor
          (sfIntrinsicModuleEquivalence Y A).inverse ≪≫
        isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
          (sfIntrinsicModuleEquivalence Y A).unitIso.symm ≪≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightUnitor)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionDirectImageIso_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : Y.ProEtᵒᵖ)
    (m : ((sfIntrinsicModuleEquivalence Y A).inverse.obj
      ((proEtaleConstantModuleDirectImage f A).obj M)).obj.obj W) :
    sectionRealization A X M ((proEtaleBaseChange f).op.obj W)
        (((sectionDirectImageIso A f).hom.app M).hom.app W m) =
      sectionRealization A Y ((proEtaleConstantModuleDirectImage f A).obj M) W m := by
  let N := (sfIntrinsicModuleEquivalence X A).inverse.obj M
  let t := (proEtaleConstantModuleDirectImage f A).map
    ((sfIntrinsicModuleEquivalence X A).counitIso.inv.app M)
  let z := (((sfIntrinsicModuleEquivalence Y A).inverse.map t).hom.app W) m
  let e := (sfIntrinsicDirectImageComparison f A).hom.app N
  let y := (((sfIntrinsicModuleEquivalence Y A).inverse.map e).hom.app W) z
  have h1 := sectionRealization_naturality A Y t W m
  have h2 := sectionRealization_naturality A Y e W z
  have h3 := sectionRealization_functor A Y
    ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W y
  let r := sectionRealization A Y ((proEtaleConstantModuleDirectImage f A).obj M) W m
  have hc : sfIntrinsicRealizationUnit Y A
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W
      (((sectionDirectImageIso A f).hom.app M).hom.app W m) =
      e.val.app W (t.val.app W r) := by
    have hδ : (sectionDirectImageIso A f).hom.app M =
        (sfIntrinsicModuleEquivalence Y A).inverse.map t ≫
          (sfIntrinsicModuleEquivalence Y A).inverse.map e ≫
            (sfIntrinsicModuleEquivalence Y A).unitIso.inv.app
              ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) := by
      dsimp only [sectionDirectImageIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
        Functor.associator_hom_app]
      simp only [Category.id_comp]
      rfl
    rw [hδ]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      CategoryTheory.comp_apply]
    change sfIntrinsicRealizationUnit Y A
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W
      (((sfIntrinsicModuleEquivalence Y A).unitIso.inv.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N)).hom.app W y) =
      e.val.app W (t.val.app W r)
    erw [← h3, h2, h1]
    rfl
  obtain ⟨a, ha⟩ := (scalarUnit_bijective A X N
    ((proEtaleBaseChange f).op.obj W)).surjective (t.val.app W r)
  have hn := (sfIntrinsicDirectImageComparison_existsUnique f A).exists.choose_spec N W a
  have hd : ((sectionDirectImageIso A f).hom.app M).hom.app W m = a := by
    apply (scalarUnit_bijective A Y
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj N) W).injective
    exact hc.trans ((congrArg (fun s ↦ e.val.app W s) ha.symm).trans hn)
  rw [hd]
  unfold sectionRealization
  rw [ha]
  change ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app M).val.app
      ((proEtaleBaseChange f).op.obj W)
      (((sfIntrinsicModuleEquivalence X A).counitIso.inv.app M).val.app
        ((proEtaleBaseChange f).op.obj W) r) = r
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    CategoryTheory.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    CategoryTheory.id_apply, t, r, sectionRealization, Functor.id_obj,
    SheafOfModules.pushforward_map_val, PresheafOfModules.pushforward_map_app_apply,
    proEtaleConstantModuleDirectImage] using
      ConcreteCategory.congr_hom
      (congrArg (fun h ↦ h.val.app ((proEtaleBaseChange f).op.obj W))
        ((sfIntrinsicModuleEquivalence X A).counitIso.inv_hom_id_app M))
      (show M.val.obj ((proEtaleBaseChange f).op.obj W) from r)

end SectionRealization

-- The coefficient transports require comparing nested pushforward module actions.
variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {T Y W : Scheme.{u}}
  [T.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [W.Over (Spec (.of P.field.k))]

end AlgebraicGeometry.Scheme

end
