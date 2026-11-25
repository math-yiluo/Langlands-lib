/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# The ordinary pro-etale unit--Leray chain formula

The module and derived units are those of the recorded constant-ring adjunction.
The terminal comparison uses its sectionwise direct image, identified with the canonical
fixed-scalar realization by the section-normalized comparison. Thus its final
map is evaluation at the actual terminal base change, X times_Y Y = X.

## References

* Stacks Project, Tags 07A6, 08J6 and 0D6E
* Tags 070I, 08BJ and 0FND
* Stacks Tags 03D1 and 0H7J
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Global sections, forgetting the locally constant scalar extension by the recorded
realization inverse. The coefficient ring is the common lift of A to the site universe. -/
noncomputable def proEtaleUnitLeraySections (X : Scheme.{u}) :=
  (sfIntrinsicModuleEquivalence X A).inverse ⋙
    Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))

/-- The recorded direct image is the direct image through the constant-section ring map:
the adjunct of the coefficient comparison is the original coefficient map, by adjunction. -/
noncomputable def proEtaleUnitLerayDirectImageIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    proEtaleConstantRingPushforward A h ≅ proEtaleConstantModuleDirectImage h A := by
  have he : proEtaleRingDirectImageMap h (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison h A) =
        proEtaleCoefficientDirectImageMap h A := by
    change (proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).symm
        (proEtaleCoefficientDirectImageMap h A)) = _
    exact Equiv.apply_symm_apply _ _
  exact SheafOfModules.pushforwardCongr
    (congrArg (fun (a : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage h CommRingCat.{u + 1}).obj (proEtaleConstantRing X A)) ↦
      (show ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y A)) ⟶
        ((proEtaleBaseChange h).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing X A)) from
        ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat RingCat)⟩)) he)

/-- Fixed-scalar terminal evaluation, using preservation of the terminal object by base change. -/
noncomputable def proEtaleUnitLerayFixedTerminalIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h ⋙
        Sheaf.Γ (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ≅
      Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
  isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ (terminalIsTerminal (C := Y.ProEt))) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    ((sheafSections _ _).mapIso
      (PreservesTerminal.iso (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h)).op).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ (terminalIsTerminal (C := X.ProEt))).symm

/-- Terminal-object identification for the recorded direct image. First identify its
coefficient map with the constant-section map by adjunction. The comparison
is normalized on scalar-unit sections. Cancel the realization equivalences and evaluate
base change at the terminal object, X times_Y Y = X. -/
noncomputable def proEtaleUnitLerayTerminalIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    proEtaleConstantRingPushforward A h ⋙ proEtaleUnitLeraySections A Y ≅
      proEtaleUnitLeraySections A X :=
  isoWhiskerRight (proEtaleUnitLerayDirectImageIso A h) (proEtaleUnitLeraySections A Y) ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso.symm
      (proEtaleConstantModuleDirectImage h A ⋙ proEtaleUnitLeraySections A Y) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (isoWhiskerRight (sfIntrinsicDirectImageComparison h A)
        (proEtaleUnitLeraySections A Y)) ≪≫
    isoWhiskerLeft ((sfIntrinsicModuleEquivalence X A).inverse ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h)
        ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
          (Sheaf.Γ (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (proEtaleUnitLerayFixedTerminalIso A h)

section UnitLerayCalculation

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {L : D ⥤ C} {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [L.Additive] [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [F.PreservesKInjectiveComplexes] (a : L ⊣ F) (e : F ⋙ G ≅ H)

-- The composition comparison carries the composite derived unit to the derived unit.
private lemma unitLerayFac :
    Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          e.hom (.up ℤ))
        DerivedCategory.Qh ≫
      H.rightDerivedFunctorUnit := by
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [Functor.rightDerivedFunctorCompIso',
    Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac
    (F ⋙ G).rightDerivedFunctor
    H.rightDerivedFunctor
    (F ⋙ G).rightDerivedFunctorUnit
    H.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ)) _

-- Compute before inverting units; no K-injectivity is required at this stage.
private lemma unitLerayHomotopy
    (K : HomotopyCategory D (.up ℤ)) :
    G.rightDerivedFunctorUnit.app K ≫
        G.rightDerivedFunctor.map
          (a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso' F G e).hom.app
            (L.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (.up ℤ)).map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
            ((L.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) := by
  let T := (L.mapHomotopyCategory (.up ℤ)).obj K
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    F.rightDerivedFunctorUnit K
  have hn := (Functor.rightDerivedFunctorCompIso' F G e).hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  have hg := G.rightDerivedFunctorUnit.naturality
    ((a.mapHomotopyCategory (.up ℤ)).unit.app K)
  have hc := NatTrans.congr_app (unitLerayFac e) T
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  dsimp only [Functor.comp_map] at hn hg
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  change DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T) ≫
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj T) = _ at hc
  rw [hi, DerivedCategory.Qh.map_id, Category.id_comp] at hc
  erw [← hn]
  erw [← Functor.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hg, hc, ← DerivedCategory.Qh.map_comp_assoc]

-- Naturality in j and inversion of the units at I and J give the chain representative.
private theorem unitLerayChain
    (I : CochainComplex D ℤ)
    (J : CochainComplex C ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    (G.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
              (whiskerRight a.unit G ≫ whiskerLeft L e.hom) (.up ℤ)).app I ≫
            (H.mapHomologicalComplex (.up ℤ)).map j) ≫
      (H.rightDerivedFunctorObjQIso J).inv =
    G.rightDerivedFunctor.map
        (a.mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Q.obj I)) ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app
        (L.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
      H.rightDerivedFunctor.map
        (L.mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map j) := by
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let U := (L.mapHomotopyCategory (.up ℤ)).obj K
  let v := (G.mapHomologicalComplex (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
      ((L.mapHomologicalComplex (.up ℤ)).obj I)
  let w :=
    (NatTrans.mapHomologicalComplex (whiskerRight a.unit G ≫ whiskerLeft L e.hom)
      (.up ℤ)).app I ≫ (H.mapHomologicalComplex (.up ℤ)).map j
  let β : G.rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
    (Functor.leftUnitor G.rightDerivedFunctor).inv ≫
      Functor.whiskerRight a.mapDerivedCategoryRightDerivedAdjunction.unit G.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L.mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso' F G e).hom
  have hquotient :
      ((G.mapHomotopyCategory (.up ℤ)).map
          ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app U) ≫
        (H.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ (.up ℤ)).map j) =
      (HomotopyCategory.quotient _ (.up ℤ)).map w := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    change (HomotopyCategory.quotient _ (.up ℤ)).map
      (v ≫ (H.mapHomologicalComplex (.up ℤ)).map j) = _
    rfl
  have hc := unitLerayHomotopy a e K
  have hj := H.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map j)
  dsimp only [Functor.comp_map] at hj
  have hc' := congrArg (fun t ↦ t ≫ H.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map j))) hc
  simp only [Category.assoc] at hc'
  erw [← hj, ← DerivedCategory.Qh.map_comp_assoc, hquotient] at hc'
  have hcomp : G.rightDerivedFunctorUnit.app K ≫ β.app (DerivedCategory.Qh.obj K) ≫
      H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map j)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map w) ≫
        H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj J) := by
    simpa only [β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
      Functor.map_comp, Category.assoc] using hc'
  -- Transport the homotopy computation along the canonical comparison with Q.
  have hfactor : L.mapDerivedCategoryFactorsh.hom.app K ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map j) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app J =
      L.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).hom.app I) ≫
        L.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map j := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    erw [DerivedCategory.Qh.map_id, Category.comp_id]
    simp only [Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality]
    erw [Iso.inv_hom_id_app_assoc]
  have hβ := β.naturality ((DerivedCategory.quotientCompQhIso _).hom.app I)
  dsimp only [Functor.comp_map] at hβ
  suffices (G.rightDerivedFunctorObjQIso I).hom ≫ DerivedCategory.Q.map w ≫
      (H.rightDerivedFunctorObjQIso J).inv =
      β.app (DerivedCategory.Q.obj I) ≫
        H.rightDerivedFunctor.map
          (L.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map j) by
    simpa only [β, w, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
      Category.assoc] using this
  rw [← cancel_epi (G.rightDerivedFunctorObjQIso I).inv, Iso.inv_hom_id_assoc]
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, asIso_hom]
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app
    ((G.mapHomologicalComplex (.up ℤ)).obj I))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  rw [reassoc_of% hβ, ← H.rightDerivedFunctor.map_comp, ← hfactor]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ H.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app J)) hcomp.symm

end UnitLerayCalculation

end AlgebraicGeometry.Scheme
