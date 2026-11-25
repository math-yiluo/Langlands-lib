/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientProjection
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedIntegralGeneratorSections
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalOrdinarySourceNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Auxiliary lemmas for the cyclic normalized source endpoint

These are split off from `DiagonalCyclicQuotientNormalizedSourceEndpoint` to keep the
memory needed to compile each module below the build limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom
  isCommMonObj_condensedRingObj Profinite.isCommMonObj_continuousMapRingObj

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction

attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  cyclicLine cyclicLineMap derivedScalars
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local semireducible] diagonalForget diagonalFiniteToPadic
attribute [local semireducible] derivedScalars
set_option backward.defeqAttrib.useBackward true
attribute [local instance 5000] sheafMonoidalCategory sheafBraidedCategory

private abbrev cyclic_source_object (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) :=
  (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
    ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
      (diagonalImmersion Y)).obj
        (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))

private theorem single_generator_injective
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U.Faithful] {P Q : A} {I : B} (g : I ⟶ U.obj P) [Epi g]
    (f h : (DerivedCategory.singleFunctor A 0).obj P ⟶
      (DerivedCategory.singleFunctor A 0).obj Q)
    (he : (DerivedCategory.singleFunctor B 0).map g ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app P ≫ U.mapDerivedCategory.map f =
      (DerivedCategory.singleFunctor B 0).map g ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app P ≫ U.mapDerivedCategory.map h) :
    f = h := by
  obtain ⟨f, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective f
  obtain ⟨h, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective h
  congr 1
  apply U.map_injective
  apply (cancel_epi g).1
  apply (DerivedCategory.singleFunctor B 0).map_injective
  have hf := (U.mapDerivedCategorySingleFunctor 0).inv.naturality f
  have hh := (U.mapDerivedCategorySingleFunctor 0).inv.naturality h
  dsimp only [Functor.comp_map] at hf hh
  have ht := he =≫ (U.mapDerivedCategorySingleFunctor 0).hom.app Q
  simpa only [Category.assoc, ← hf, ← hh, Iso.inv_hom_id_app,
    Category.comp_id, ← CategoryTheory.Functor.map_comp] using ht

private theorem single_limit_projection
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H) (a : K ≅ (DerivedCategory.singleFunctor _ 0).obj H)
    (n : ℕ) :
    diagonalSingleLimitComparison F L P H K s a ≫ (L.projection n).app K ≫
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map a.hom ≫
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app H =
      (F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        (DerivedCategory.singleFunctor B 0).map (s.hom ≫ limit.π H (op n)) := by
  unfold diagonalSingleLimitComparison
  simp only [Category.assoc]
  erw [(L.projection n).naturality_assoc]
  simp only [← CategoryTheory.Functor.map_comp_assoc, a.inv_hom_id]
  erw [((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map_id, Category.id_comp]
  erw [DiagonalTrace.ordinaryRlim_projection, ← CategoryTheory.Functor.map_comp]

private theorem exact_scalar_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (R : B ⥤ A) (U : A ⥤ C) [R.Additive] [U.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (L : DerivedCategory A ⥤ DerivedCategory B) (adj : L ⊣ R.mapDerivedCategory)
    (M : A) (N : B) (d : L.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      (DerivedCategory.singleFunctor B 0).obj N) (m : M ⟶ R.obj N)
    (hd : adj.unit.app _ ≫ R.mapDerivedCategory.map d =
      (DerivedCategory.singleFunctor A 0).map m ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app N) :
    ((Functor.whiskerRight adj.unit U.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L
        ((Functor.mapDerivedCategoryCompIso R U) ≪≫
          Iso.refl (R ⋙ U).mapDerivedCategory).hom).app
            ((DerivedCategory.singleFunctor A 0).obj M)) ≫
      (R ⋙ U).mapDerivedCategory.map d ≫
      ((R ⋙ U).mapDerivedCategorySingleFunctor 0).hom.app N =
    (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor C 0).map (U.map m) := by
  have hn := (Functor.mapDerivedCategoryCompIso R U).hom.naturality d
  dsimp only [Functor.comp_map] at hn
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
    NatTrans.id_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← reassoc_of% hn, ← U.mapDerivedCategory.map_comp_assoc, hd]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor R U N]
  simp only [Iso.hom_inv_id_app_assoc, ← U.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  exact (congrArg (fun f ↦ U.mapDerivedCategory.map f ≫
      (U.mapDerivedCategorySingleFunctor 0).hom.app (R.obj N))
        (Category.comp_id ((DerivedCategory.singleFunctor A 0).map m))).trans
    ((U.mapDerivedCategorySingleFunctor 0).hom.naturality m)

private theorem scalar_unit_endpoint
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)]
    {M : Modules Λ X} {N : Modules Λ' X} {m : M.X ⟶ N.X}
    (d : Endpoint a M N m) :
    (scalarUnderlyingUnit a X).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (Mod.forget _).mapDerivedCategory.map d.iso.hom ≫
        ((Mod.forget _).mapDerivedCategorySingleFunctor 0).hom.app N =
      ((Mod.forget _).mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor (DiagonalAb X) 0).map d.semilinear.hom.hom := by
  let R := Mod.comap (D := DiagonalAb X) (coefficientMap a X)
  let U := Mod.forget (D := DiagonalAb X) (condensedRingObj Λ X)
  let V := Mod.forget (D := DiagonalAb X) (condensedRingObj Λ' X)
  let L := derivedScalars a X
  let adj : derivedScalars a X ⊣ R.mapDerivedCategory :=
    @Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (condensedRingObj Λ X) (condensedRingObj Λ' X) _ _
      (isCommMonObj_condensedRingObj Λ X) (isCommMonObj_condensedRingObj Λ' X)
      (coefficientMap a X) _
  have hd : adj.unit.app _ ≫ R.mapDerivedCategory.map d.iso.hom =
      (DerivedCategory.singleFunctor _ 0).map d.semilinear.hom ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app N := by
    have hd := d.normalization
    change adj.homEquiv _ _ d.iso.hom = _ at hd
    erw [Adjunction.homEquiv_unit] at hd
    exact hd
  exact exact_scalar_unit R U L adj M N d.iso.hom d.semilinear.hom hd

private theorem exact_underlying_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : A ⥤ B) (H : B ⥤ C) (U : C ⥤ D) (V : A ⥤ D)
    [G.Additive] [H.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : G ⋙ H ⋙ U ≅ V) (Y : A) :
    U.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).inv.app (G.obj Y)) ≫
      U.mapDerivedCategory.map
        (H.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).inv.app Y)) ≫
      (Functor.mapDerivedCategoryCompIso H U).hom.app
        (G.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj Y)) ≫
      (Functor.mapDerivedCategoryCompIso G (H ⋙ U)).hom.app
        ((DerivedCategory.singleFunctor A 0).obj Y) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor A 0).obj Y) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app Y =
    (U.mapDerivedCategorySingleFunctor 0).hom.app (H.obj (G.obj Y)) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app Y) := by
  have hn := (Functor.mapDerivedCategoryCompIso H U).hom.naturality
    ((G.mapDerivedCategorySingleFunctor 0).inv.app Y)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor G (H ⋙ U) Y]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [(H ⋙ U).mapDerivedCategory.map_id, Category.id_comp]
  erw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor H U (G.obj Y)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [U.mapDerivedCategory.map_id, Category.id_comp]

private theorem epi_iso_composite {C : Type*} [Category C]
    {X Y Z : C} (f : X ⟶ Y) (hf : Epi f) (e : Y ≅ Z) : Epi (f ≫ e.hom) := by
  have : Epi f := hf
  infer_instance

private theorem cyclic_generator_epi (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) :
    Epi (cartierProIntegralGenerator (diagonalResidue.{u} l n) (diagonalImmersion Y)) := by
  let A := diagonalResidue.{u} l n
  let X := ProjectiveLine Y
  let J := Scheme.ProEt.topology X
  let f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ AddCommGrpCat.of A :=
    AddCommGrpCat.ofHom ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom)
  have : Epi f := by
    erw [AddCommGrpCat.epi_iff_surjective]
    intro x
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective x.down
    exact ⟨ULift.up a, ULift.ext ha⟩
  have he : constantGenerator A X =
      (constantSheaf J Ab.{u + 1}).map f ≫ (finiteConstantAbComparison A X).inv := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _
      ((cartierForget A X).obj (geoCartierConstant A X)).property
    ext V x
    have h := congrArg (fun z ↦ z.app V x) (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map f))
    change _ = (finiteConstantAbComparison A X).inv.hom.app V
      (((constantSheaf J Ab.{u + 1}).map f).hom.app V
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V x))
    change (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app V
        (f x) = ((constantSheaf J Ab.{u + 1}).map f).hom.app V
          ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V x) at h
    erw [← h]
    exact (constantGenerator_spec A X V x.down).trans
      (constant_forget_inv_generator A X V (x.down : A)).symm
  have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine Y ↘ Y)
  have : LocallyOfFinitePresentation (ProjectiveLine Y ↘ Y) := inferInstance
  have : LocallyOfFinitePresentation (diagonalImmersion Y) := by
    change LocallyOfFinitePresentation (pullback.diagonal (ProjectiveLine Y ↘ Y))
    infer_instance
  have : PreservesColimits (constantSheaf J Ab.{u + 1}) :=
    (constantSheafAdj J Ab.{u + 1} (Scheme.ProEt.isTerminalMkId X)).leftAdjoint_preservesColimits
  have hEf : Epi ((constantSheaf J Ab.{u + 1}).map f) := inferInstance
  have hE : Epi ((constantSheaf J Ab.{u + 1}).map f ≫
      (finiteConstantAbComparison A X).inv) :=
    epi_iso_composite _ hEf (finiteConstantAbComparison A X).symm
  have : Epi (constantGenerator A X) := by
    rw [he]
    exact hE
  erw [supportedGenerator_eq]
  exact epi_lowerStar_map_of_isFinite_ab (diagonalImmersion Y) (constantGenerator A X)

private theorem three_source_underlying
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : A ⥤ B) (H : B ⥤ C) (U : C ⥤ D) (V : A ⥤ D)
    [G.Additive] [H.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : G ⋙ H ⋙ U ≅ V) (Y : A) {Z : B} (s : G.obj Y ≅ Z)
    (Q : DerivedCategory A) (q : (DerivedCategory.singleFunctor A 0).obj Y ≅ Q) :
    let c : G.mapDerivedCategory ⋙ H.mapDerivedCategory ⋙ U.mapDerivedCategory ≅
        V.mapDerivedCategory :=
      Functor.isoWhiskerLeft G.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso H U) ≪≫
      (Functor.mapDerivedCategoryCompIso G (H ⋙ U)) ≪≫
      Functor.mapDerivedCategoryNatIso e
    U.mapDerivedCategory.map
      ((H.mapDerivedCategorySingleFunctor 0).inv.app Z ≫
        H.mapDerivedCategory.map
          ((DerivedCategory.singleFunctor B 0).map s.inv ≫
            (G.mapDerivedCategorySingleFunctor 0).inv.app Y ≫
            G.mapDerivedCategory.map q.hom)) ≫
      c.hom.app Q ≫ V.mapDerivedCategory.map q.inv ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app Y =
    (U.mapDerivedCategorySingleFunctor 0).hom.app (H.obj Z) ≫
      (DerivedCategory.singleFunctor D 0).map
        ((H ⋙ U).map s.inv ≫ e.hom.app Y) := by
  dsimp only
  let c : G.mapDerivedCategory ⋙ H.mapDerivedCategory ⋙ U.mapDerivedCategory ≅
      V.mapDerivedCategory :=
    Functor.isoWhiskerLeft G.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso H U) ≪≫
    (Functor.mapDerivedCategoryCompIso G (H ⋙ U)) ≪≫
    Functor.mapDerivedCategoryNatIso e
  have hn := c.hom.naturality q.hom
  dsimp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  simp only [← V.mapDerivedCategory.map_comp_assoc, q.hom_inv_id,
    V.mapDerivedCategory.map_id, Category.id_comp]
  have hs := (H.mapDerivedCategorySingleFunctor 0).inv.naturality s.inv
  dsimp only [Functor.comp_map] at hs
  erw [← U.mapDerivedCategory.map_comp_assoc, ← hs, U.mapDerivedCategory.map_comp]
  have hu := (U.mapDerivedCategorySingleFunctor 0).hom.naturality (H.map s.inv)
  dsimp only [Functor.comp_map] at hu
  dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [exact_underlying_single G H U V e Y]
  erw [reassoc_of% hu]
  simp only [Functor.comp_map]

-- `three_source_underlying` with the source folded into `threeFunctorSource`, so that it
-- applies to `cyclicFiniteEvaluationSource` without the kernel unfolding the composite.
private theorem three_source_folded
    {A₁ A B C D : Type*} [Category A₁] [Category A] [Category B] [Category C] [Category D]
    [Abelian A₁] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A₁] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : DerivedCategory A₁ ⥤ DerivedCategory A)
    (G : A ⥤ B) (H : B ⥤ C) (U : C ⥤ D) (V : A ⥤ D)
    [G.Additive] [H.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : G ⋙ H ⋙ U ≅ V) (Y : A) {Z : B} (s : G.obj Y ≅ Z) (X₁ : A₁)
    (q : (DerivedCategory.singleFunctor A 0).obj Y ≅
      R.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁)) :
    U.mapDerivedCategory.map (threeFunctorSource R G H q.hom s) ≫
      (Functor.isoWhiskerLeft G.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso H U) ≪≫
        (Functor.mapDerivedCategoryCompIso G (H ⋙ U)) ≪≫
        Functor.mapDerivedCategoryNatIso e).hom.app
          (R.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁)) ≫
      V.mapDerivedCategory.map q.inv ≫ (V.mapDerivedCategorySingleFunctor 0).hom.app Y =
    (U.mapDerivedCategorySingleFunctor 0).hom.app (H.obj Z) ≫
      (DerivedCategory.singleFunctor D 0).map ((H ⋙ U).map s.inv ≫ e.hom.app Y) := by
  have h := three_source_underlying G H U V e Y s _ q
  unfold threeFunctorSource
  exact h

open CategoryTheory.MonoidalCategory MonObj in
private theorem completed_generator_unit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    diagonalCompletedGenerator l Y =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        η[(completedAbFunctor (ProjectiveLine Y)).obj
          (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)] := by
  apply (diagonalCompletedGenerator_existsUnique l Y).unique
    (diagonalCompletedGenerator_existsUnique l Y).exists.choose_spec
  intro U n
  let X := ProjectiveLine Y
  let J := Scheme.ProEt.topology X
  let V := op ((Scheme.proEtaleBaseChange (diagonalImmersion Y)).obj U.unop)
  let S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (Scheme.purTwistZlCompletion X l)
  have h := ConcreteCategory.congr_hom
    (congr_app (Sheaf.ε_sheafToPresheaf_comp_map_one_sheafCompose J S) V)
      (ULift.up n)
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) =
      (sheafificationAdjunction J Ab.{u + 1}).unit.app
        (𝟙_ (X.ProEtᵒᵖ ⥤ Ab.{u + 1})) := by
    change (sheafificationAdjunction J Ab.{u + 1}).unit.app _ ≫
      (sheafToPresheaf J Ab.{u + 1}).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [hε] at h
  change (η[(completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)]).hom.app V
    ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up n)) = _ at h
  erw [Functor.one_compForget₂_app, AddCommGrpCat.ringMonObj_one_apply] at h
  apply heq_of_eq
  have hncast : (n : (Scheme.purTwistZlCompletion X l).obj.obj V) =
      n • (1 : (Scheme.purTwistZlCompletion X l).obj.obj V) := (zsmul_one n).symm
  exact h.trans hncast

open CategoryTheory.MonoidalCategory MonObj in
private theorem finite_generator_unit
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    cartierProIntegralGenerator A (diagonalImmersion Y) ≫
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (finiteConstantAbComparison A (ProjectiveLine Y)).hom =
    (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
      η[((sfbConstantRing (ProjectiveLine Y)).obj (RingCat.of A)).X] := by
  erw [supportedGenerator_eq, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteConstantAbRing A (ProjectiveLine Y)).property
  ext V x
  change (finiteConstantAbComparison A (ProjectiveLine Y)).hom.hom.app V
      ((constantGenerator A (ProjectiveLine Y)).hom.app V
        ((toSheafify (Scheme.ProEt.topology (ProjectiveLine Y))
          ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V x)) = _
  obtain ⟨x⟩ := x
  erw [constantGenerator_spec, constant_forget_generator]
  let J := Scheme.ProEt.topology (ProjectiveLine Y)
  let F := constantSheaf J Ab.{u + 1}
  have hc : Functor.LaxMonoidal.ε F = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (Category.id_comp _).trans ((presheafToSheaf J Ab.{u + 1}).map_id _)
  change _ = ((Functor.LaxMonoidal.ε F ≫ F.map η[AddCommGrpCat.of A]).hom.app V)
    ((toSheafify J ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up x))
  erw [hc, Category.id_comp]
  have h := ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality J
      ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).map η[AddCommGrpCat.of A])) V)
        (ULift.up x)
  change (toSheafify J ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
      (AddCommGrpCat.of A))).app V (x : A) =
    (F.map η[AddCommGrpCat.of A]).hom.app V
      ((toSheafify J ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up x)) at h
  exact h

private theorem map_iso_mono {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y : A} (e : X ≅ Y) : Mono (F.map e.hom) := inferInstance

private theorem generator_comparison
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {I R S T Q V : A} {X₃ X₆ : B}
    (ηR : I ⟶ R) (v : R ⟶ S) (a : S ⟶ T) (u : T ⟶ Q) (k : Q ⟶ V)
    (ηS : I ⟶ S) (w : T ⟶ V) (ηV : I ⟶ V)
    (γ : F.obj I ⟶ F.obj R) (b : F.obj R ⟶ X₃) (c : X₃ ⟶ F.obj S)
    (d : F.obj S ⟶ F.obj T) (e : F.obj T ⟶ X₆) (f : X₆ ⟶ F.obj Q)
    (g : F.obj I ⟶ F.obj Q)
    (hγ : γ = F.map ηR) (hn : b ≫ c = F.map v)
    (hd : d = F.map a) (hp : e ≫ f = F.map u)
    (hu : u ≫ k = w) (hv : ηR ≫ v = ηS) (hw : ηS ≫ a ≫ w = ηV)
    (hg : g ≫ F.map k = F.map ηV) [Mono (F.map k)] :
    γ ≫ b ≫ c ≫ d ≫ e ≫ f = g := by
  apply (cancel_mono (F.map k)).mp
  calc
    _ = γ ≫ (b ≫ c) ≫ d ≫ (e ≫ f) ≫ F.map k := by
      simp only [Category.assoc]
    _ = F.map (ηR ≫ v ≫ a ≫ u ≫ k) := by
      rw [hγ, hn, hd, hp]
      simp only [CategoryTheory.Functor.map_comp]
    _ = F.map ηV := by
      congr 1
      rw [hu, ← Category.assoc ηR v, hv, hw]
    _ = _ := hg.symm

open CategoryTheory.MonoidalCategory MonObj in
private theorem source_generator_normalized
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (hn : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫
      sourceIso.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom)))
    (p : CyclicCartierFrame l Y n) :
    diagonalCompletedGenerator l Y ≫ eW.underlying.inv.app (diagonalCompletedSource l Y) ≫
      sourceIso.hom.hom ≫ p.supported.semilinear.hom.hom ≫
      p.eW.underlying.inv.app _ ≫
      (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)).map
        p.sourceComparison.iso.hom =
    cartierProIntegralGenerator (diagonalResidue.{u} l n) (diagonalImmersion Y) := by
  let X := ProjectiveLine Y
  let i := diagonalImmersion Y
  let F := lowerStar Ab.{u + 1} i
  let v := eP.underlying.inv.app (SheafOfModules.unit
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≫ eP.unitIso.hom.hom
  let V := cartierForget (diagonalResidue.{u} l n) X
  have hp := eq_of_heq p.sourceComparison.normalization
  have hsup := supported_endpoint_underlying (p.units X) p.supported
  have hunit := p.eP.unit_normalization
  change p.eP.underlying.inv.app _ ≫ V.map p.eP.unitIso.hom ≫
    (finiteConstantAbComparison (diagonalResidue.{u} l n) X).hom =
    p.eP.coefficient.hom.hom at hunit
  have hv := unitRealization_one l X eP
  change η[(completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)] ≫ v =
    η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] at hv
  have hw : η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] ≫
      coefficientMap (cyclicMap l n) X ≫ p.eP.coefficient.hom.hom =
      η[((sfbConstantRing X).obj (RingCat.of (diagonalResidue.{u} l n))).X] :=
    (Category.assoc _ _ _).symm.trans
      (((IsMonHom.one_hom (f := coefficientMap (cyclicMap l n) X)) =≫
        p.eP.coefficient.hom.hom).trans
          (IsMonHom.one_hom (f := p.eP.coefficient.hom.hom)))
  have : Mono (F.map (finiteConstantAbComparison (diagonalResidue.{u} l n) X).hom) :=
    map_iso_mono F (finiteConstantAbComparison (diagonalResidue.{u} l n) X)
  exact generator_comparison F _ v (coefficientMap (cyclicMap l n) X) _
    (finiteConstantAbComparison (diagonalResidue.{u} l n) X).hom
    _ p.eP.coefficient.hom.hom _ _ _ _ _ _ _ _
    (completed_generator_unit l Y) (eq_of_heq hn) hsup hp hunit hv hw
    (finite_generator_unit (diagonalResidue.{u} l n) Y)

private theorem exact_square_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (V : B ⥤ D) (F : A ⥤ C) (R : C ⥤ D)
    [U.Additive] [V.Additive] [F.Additive] [R.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : U ⋙ V ≅ F ⋙ R) (M : A) :
    ((Functor.mapDerivedCategoryCompIso U V) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F R).symm).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M) ≫
      R.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (R.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) =
    V.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem completed_underlying_single
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) :
    let Z := diagonalCompletedRestriction l (diagonalSurface Y)
    let U := diagonalForget l (diagonalSurface Y)
    let V := Mod.forget (D := DiagonalAb (diagonalSurface Y))
      (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))
    let P := diagonalCompletedSource l Y
    U.mapDerivedCategory.map ((Z.mapDerivedCategorySingleFunctor 0).inv.app P) ≫
      (cyclicCompletedUnderlying l Y eW).hom.app (diagonalCompletedDomain l Y) ≫
      V.mapDerivedCategory.map ((eW.F.mapDerivedCategorySingleFunctor 0).hom.app P) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (eW.F.obj P) =
    (U.mapDerivedCategorySingleFunctor 0).hom.app (Z.obj P) ≫
      (DerivedCategory.singleFunctor _ 0).map (eW.underlying.inv.app P) := by
  dsimp only
  erw [show (cyclicCompletedUnderlying l Y eW).hom.app (diagonalCompletedDomain l Y) ≫
      _ ≫ _ = _ from exact_square_single _ _ _ _ eW.underlying.symm
        (diagonalCompletedSource l Y)]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

private theorem mapped_source_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (U : B ⥤ C) (V : A ⥤ C) (c : F ⋙ U ⟶ V)
    {X Y Z : A} {P : B} {Q : C} (a : P ⟶ F.obj X) (q : Y ≅ X)
    (r0 : X ⟶ Z) (r : V.obj Z ⟶ Q) :
    U.map (a ≫ F.map q.inv) ≫ c.app Y ≫ V.map (q.hom ≫ r0) ≫ r =
      U.map a ≫ c.app X ≫ V.map r0 ≫ r := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := c.naturality q.inv
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← V.map_comp_assoc, q.inv_hom_id_assoc]

private theorem iso_source_cancel
    {C : Type*} [Category C] {A B D : C} (e : A ≅ B) (s : A ≅ D) :
    (s.inv ≫ (𝟙 A ≫ e.hom)) ≫ (e.inv ≫ s.hom) = 𝟙 D := by
  simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]

private theorem map_finish
    {A B : Type*} [Category A] [Category B] (S : A ⥤ B)
    {I J : A} {X Y Z W : B} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ W) (d : W ⟶ S.obj I)
    (j : X ⟶ S.obj J) (k : J ⟶ I) (m : I ⟶ J)
    (h : a ≫ b ≫ c ≫ d = j ≫ S.map k) (hm : k ≫ m = 𝟙 J) :
    a ≫ b ≫ c ≫ d ≫ S.map m = j := by
  simpa only [Category.assoc, ← S.map_comp, hm, S.map_id, Category.comp_id] using
    congrArg (fun f ↦ f ≫ S.map m) h

private theorem cyclic_source_forward
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (p : CyclicCartierFrame l Y n) :
    let U := diagonalForget l (diagonalSurface Y)
    let V := Mod.forget (D := DiagonalAb (diagonalSurface Y))
      (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) (diagonalSurface Y))
    let R := derivedScalars (cyclicMap l n) (diagonalSurface Y)
    let P := diagonalCompletedSource l Y
    let N := source (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) Y
    let q := (eW.F.mapDerivedCategorySingleFunctor 0).app P ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso sourceIso
    let m := p.eW.underlying.inv.app N ≫
      (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)).map
        p.sourceComparison.iso.hom
    let c := (cyclicEvaluationUnderlying l Y n eW p).hom.app
        (diagonalCompletedDomain l Y) ≫
      V.mapDerivedCategory.map (R.map q.hom ≫ p.supported.iso.hom) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor _ 0).map m
    U.mapDerivedCategory.map (cyclicEvaluationSource l Y n eW sourceIso p) ≫ c =
      (U.mapDerivedCategorySingleFunctor 0).hom.app (cyclic_source_object l Y n) := by
  dsimp only
  let U := diagonalForget l (diagonalSurface Y)
  let V := Mod.forget (D := DiagonalAb (diagonalSurface Y))
    (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) (diagonalSurface Y))
  let R := derivedScalars (cyclicMap l n) (diagonalSurface Y)
  let P := diagonalCompletedSource l Y
  let N := source (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) Y
  let q := (eW.F.mapDerivedCategorySingleFunctor 0).app P ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso sourceIso
  let d := Functor.isoWhiskerLeft p.eW.F.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso
        (diagonalFiniteToPadic l n (diagonalSurface Y)) U) ≪≫
    (Functor.mapDerivedCategoryCompIso p.eW.F
      (diagonalFiniteToPadic l n (diagonalSurface Y) ⋙ U)) ≪≫
    Functor.mapDerivedCategoryNatIso (cyclicFiniteUnderlying l Y n p)
  have hf := three_source_folded R p.eW.F
    (diagonalFiniteToPadic l n (diagonalSurface Y)) U V
    (cyclicFiniteUnderlying l Y n p) N p.sourceComparison.iso
    (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) p.supported.iso.symm
  let m := p.eW.underlying.inv.app N ≫
    (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)).map
      p.sourceComparison.iso.hom
  let k := (diagonalFiniteToPadic l n (diagonalSurface Y) ⋙ U).map
    p.sourceComparison.iso.inv ≫ (cyclicFiniteUnderlying l Y n p).hom.app N
  have hm : k ≫ m = 𝟙 _ := by
    unfold k m cyclicFiniteUnderlying diagonalFiniteForgetIso
    exact iso_source_cancel (p.eW.underlying.app N)
      ((cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)).mapIso
        p.sourceComparison.iso)
  have hfinish := map_finish (DerivedCategory.singleFunctor _ 0)
    (U.mapDerivedCategory.map (cyclicFiniteEvaluationSource l Y n p))
    (d.hom.app (R.obj ((DerivedCategory.singleFunctor _ 0).obj
      (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y))))
    (V.mapDerivedCategory.map p.supported.iso.hom)
    ((V.mapDerivedCategorySingleFunctor 0).hom.app N)
    ((U.mapDerivedCategorySingleFunctor 0).hom.app (cyclic_source_object l Y n))
    k m hf hm
  have htransport := mapped_source_transport
    (p.eW.F.mapDerivedCategory ⋙
      (diagonalFiniteToPadic l n (diagonalSurface Y)).mapDerivedCategory)
    U.mapDerivedCategory V.mapDerivedCategory d.hom
    (cyclicFiniteEvaluationSource l Y n p) (R.mapIso q) p.supported.iso.hom
    ((V.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor _ 0).map m)
  unfold cyclicEvaluationSource completedFunctorSource
  exact htransport.trans hfinish

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
