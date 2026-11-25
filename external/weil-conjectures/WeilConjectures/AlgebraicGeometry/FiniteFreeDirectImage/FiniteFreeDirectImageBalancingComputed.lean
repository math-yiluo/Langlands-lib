/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Normalization of the scalar and geometric balancing comparison

Source: Stacks Project, Tags 03EL, 0D6D and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

/-- The ordinary balancing conjugates the identity-on-sections restriction square.
Source: Stacks Project, Tag 03EL.
(blueprint: lem-sp-finite-free-direct-image-balancing-computed). -/
def ordinaryBalancing {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    (sW.presentation a.target).ordinary ⋙
        proEtaleRingModulePullback q S.target S.source S.identification ≅
      proEtaleRingModulePullback q R.target R.source R.identification ⋙
        (sZ.presentation a.source).ordinary :=
  ((conjugateIsoEquiv
      ((sW.normalization.ordinaryAdjunction a.target).comp
        (proEtaleRingModuleAdjunction q S.target S.source S.identification))
      ((proEtaleRingModuleAdjunction q R.target R.source R.identification).comp
        (sZ.normalization.ordinaryAdjunction a.source))).symm
    (proEtaleRingRestrictionDirectImage q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)).symm

/-- A comparison is computed by ordinary balancing when it intertwines both
universal derived counits with the termwise ordinary comparison.
Source: Stacks Project, Tags 06YY and 07A6.
(blueprint: lem-sp-finite-free-direct-image-balancing-computed). -/
def BalancingComputed {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S)
    (β : (sW.presentation a.target).derived ⋙
        proEtaleRingDerivedPullback q S.target S.source S.identification ≅
      proEtaleRingDerivedPullback q R.target R.source R.identification ⋙
        (sZ.presentation a.source).derived) : Prop :=
  ∀ H : HomotopyCategory (proEtaleRingModules W R.target) (.up ℤ),
    β.hom.app (DerivedCategory.Qh.obj H) ≫
        (sZ.presentation a.source).derived.map
          ((proEtaleRingModulePullback q R.target R.source
            R.identification).mapDerivedCategoryFactorsh.hom.app H) ≫
        (sZ.presentation a.source).counit.app
          (((proEtaleRingModulePullback q R.target R.source
            R.identification).mapHomotopyCategory (.up ℤ)).obj H) =
      (proEtaleRingDerivedPullback q S.target S.source S.identification).map
          ((sW.presentation a.target).counit.app H) ≫
        (proEtaleRingModulePullback q S.target S.source
          S.identification).mapDerivedCategoryFactorsh.hom.app
            (((sW.presentation a.target).ordinary.mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl
              ((sW.presentation a.target).ordinary ⋙
                proEtaleRingModulePullback q S.target S.source S.identification))
              (.up ℤ)).hom.app H ≫
            ((ordinaryBalancing sW sZ a).hom.mapHomotopyCategory (.up ℤ)).app H ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl
              (proEtaleRingModulePullback q R.target R.source R.identification ⋙
                (sZ.presentation a.source).ordinary)) (.up ℤ)).inv.app H)

private theorem scalar_hom_comparison {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ))
    (K : HomotopyCategory (proEtaleRingModules X S) (.up ℤ))
    (f : ((s.presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj H ⟶ K) :
    (s.adjunction a).homEquiv _ _
        ((s.presentation a).counit.app H ≫ DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map
          (((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).homEquiv
            H K f) ≫
        (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.inv.app K := by
  obtain ⟨d, hd⟩ := SheafOfModules.sheafRingDerivedHomComparison a
    (s.presentation a).ordinary (s.presentation a).obj_eq (s.presentation a).map_eq
    (s.normalization.ordinaryAdjunction a) (s.presentation a).derived
    (s.presentation a).counit (s.presentation a).universal
  have he : s.adjunction a = d := by
    apply Adjunction.ext
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ))
    intro M
    obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
    obtain ⟨P, f, hP, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) C
    have hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology X) (R := R) (P.X n) := fun n ↦
      (exactFunctor (proEtaleRingModules X R) (proEtaleRingModules X R)).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
          (J := ProEt.topology X) R (P.X n)).symm (hf n)
    let T := (HomotopyCategory.quotient _ _).obj P
    have hc : IsIso ((s.presentation a).counit.app T) :=
      s.normalization.computed a P hP hflat
    let _ := hc
    have hp : (s.adjunction a).unit.app (DerivedCategory.Qh.obj T) =
        d.unit.app (DerivedCategory.Qh.obj T) := by
      apply (cancel_mono ((proEtaleRingRestrictScalars a).mapDerivedCategory.map
        ((s.presentation a).counit.app T) ≫
          (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
            (((s.presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj T))).1
      have hh := hd T (((s.presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj T)
        (𝟙 _)
      simp only [Adjunction.homEquiv_apply, CategoryTheory.Functor.map_id] at hh
      repeat erw [CategoryTheory.Category.comp_id] at hh
      have hh' := congrArg (fun k ↦ k ≫
        (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
          (((s.presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj T)) hh
      simp only [Category.assoc, Iso.inv_hom_id_app] at hh'
      repeat erw [CategoryTheory.Category.comp_id] at hh'
      exact (s.adjunction_unit a P hP hflat).trans hh'.symm
    let g := DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f)
    have hg : IsIso g := Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq)
    let _ := hg
    apply (cancel_epi g).1
    have hn := (s.adjunction a).unit.naturality g
    have hn' := d.unit.naturality g
    simp only [CategoryTheory.Functor.id_map] at hn hn'
    rw [hn, hn', hp]
  rw [he]
  exact hd H K f

private theorem scalar_unit {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ)) :
    (s.adjunction a).unit.app (DerivedCategory.Qh.obj H) ≫
        (proEtaleRingRestrictScalars a).mapDerivedCategory.map
          ((s.presentation a).counit.app H) =
      DerivedCategory.Qh.map
          (((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).unit.app H) ≫
        (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.inv.app
          (((s.presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj H) := by
  have h := scalar_hom_comparison s a H _ (𝟙 _)
  simp only [Adjunction.homEquiv_apply, CategoryTheory.Functor.map_id] at h
  repeat erw [CategoryTheory.Category.comp_id] at h
  exact h

private theorem scalar_counit {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (K : HomotopyCategory (proEtaleRingModules X S) (.up ℤ)) :
    (s.presentation a).derived.map
        ((proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.inv.app K) ≫
        (s.adjunction a).counit.app (DerivedCategory.Qh.obj K) =
      (s.presentation a).counit.app
          (((proEtaleRingRestrictScalars a).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).counit.app
            K) := by
  have hid : ((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).homEquiv
      _ K (((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).counit.app K) =
        𝟙 _ :=
    ((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).right_triangle_components K
  have h := scalar_hom_comparison s a _ K
    (((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).counit.app K)
  rw [hid, CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp] at h
  have h' := congrArg ((s.adjunction a).homEquiv _ _).symm h
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply] using h'.symm

private theorem exactSquare_factorsh
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) (L' : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : G ⋙ L' ≅ L ⋙ H) (K : HomotopyCategory A (.up ℤ)) :
    (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso L H).symm).hom.app
          (DerivedCategory.Qh.obj K) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory s.hom (.up ℤ)).app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fach L H K
  have h₂ := Functor.mapDerivedCategoryCompIso_fach G L' K
  have h₃ := Functor.mapDerivedCategoryNatIso_fach s K
  apply (cancel_mono (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁, h₃, ← h₂]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  have hc : DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [hc, Category.comp_id]

private theorem homotopy_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : HomotopyCategory B (.up ℤ)) :
    (mateEquiv (adj.mapHomotopyCategory (.up ℤ)) (adj'.mapHomotopyCategory (.up ℤ))
      (TwoSquare.mk _ _ _ _
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom ≫
          NatTrans.mapHomotopyCategory s.hom (.up ℤ) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv))).app K =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)) (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    CategoryTheory.Category.id_comp]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Functor.mapHomologicalComplexCompIso]
  simp only [ NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    CategoryTheory.Category.id_comp]
  simp only [Functor.id_obj, NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, NatIso.mapHomologicalComplex_inv_app_f, Iso.refl_inv,
    Functor.map_comp, HomologicalComplex.id_f, Category.comp_id, Category.assoc,
    Functor.comp_map]
  change adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (𝟙 (L'.obj (G.obj (R.obj (K.X n))))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (𝟙 (H.obj (L.obj (R.obj (K.X n))))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) =
    𝟙 _ ≫ adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [R'.map_id, CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp]

private theorem mate_factors
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {G₁ : C₁ ⥤ C₂} {F₁ : C₂ ⥤ C₁} (a₁ : G₁ ⊣ F₁)
    {G₂ : C₃ ⥤ C₄} {F₂ : C₄ ⥤ C₃} (a₂ : G₂ ⊣ F₂)
    {H₁ : C₁ ⥤ C₃} {H₂ : C₂ ⥤ C₄}
    {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₃ : C₃ ⥤ D₃} {Q₄ : C₄ ⥤ D₄}
    {L₁ : D₁ ⥤ D₂} {R₁ : D₂ ⥤ D₁} (b₁ : L₁ ⊣ R₁)
    {L₂ : D₃ ⥤ D₄} {R₂ : D₄ ⥤ D₃} (b₂ : L₂ ⊣ R₂)
    {T₁ : D₁ ⥤ D₃} {T₂ : D₂ ⥤ D₄}
    (α₁ : Q₁ ⋙ L₁ ⟶ G₁ ⋙ Q₂) (β₁ : F₁ ⋙ Q₁ ⟶ Q₂ ⋙ R₁)
    (α₂ : Q₃ ⋙ L₂ ⟶ G₂ ⋙ Q₄) (β₂ : F₂ ⋙ Q₃ ⟶ Q₄ ⋙ R₂)
    (γ₁ : Q₁ ⋙ T₁ ⟶ H₁ ⋙ Q₃) (γ₂ : Q₂ ⋙ T₂ ⟶ H₂ ⋙ Q₄)
    (hu : ∀ M : C₃, b₂.unit.app (Q₃.obj M) ≫ R₂.map (α₂.app M) =
      Q₃.map (a₂.unit.app M) ≫ β₂.app (G₂.obj M))
    (hc : ∀ K : C₂, L₁.map (β₁.app K) ≫ b₁.counit.app (Q₂.obj K) =
      α₁.app (F₁.obj K) ≫ Q₂.map (a₁.counit.app K))
    (σ : TwoSquare H₁ G₁ G₂ H₂) (θ : TwoSquare T₁ L₁ L₂ T₂)
    (K : C₂)
    (hθ : θ.app (Q₁.obj (F₁.obj K)) ≫ T₂.map (α₁.app (F₁.obj K)) ≫
        γ₂.app (G₁.obj (F₁.obj K)) =
      L₂.map (γ₁.app (F₁.obj K)) ≫ α₂.app (H₁.obj (F₁.obj K)) ≫
        Q₄.map (σ.app (F₁.obj K))) :
    T₁.map (β₁.app K) ≫ (mateEquiv b₁ b₂ θ).app (Q₂.obj K) ≫
        R₂.map (γ₂.app K) =
      γ₁.app (F₁.obj K) ≫ Q₃.map ((mateEquiv a₁ a₂ σ).app K) ≫
        β₂.app (H₂.obj K) := by
  have hmate (Z : D₂) : (mateEquiv b₁ b₂ θ).app Z =
      b₂.unit.app (T₁.obj (R₁.obj Z)) ≫ R₂.map (θ.app (R₁.obj Z)) ≫
        R₂.map (T₂.map (b₁.counit.app Z)) := by simp [mateEquiv_apply]
  have hmate' : (mateEquiv a₁ a₂ σ).app K =
      a₂.unit.app (H₁.obj (F₁.obj K)) ≫ F₂.map (σ.app (F₁.obj K)) ≫
        F₂.map (H₂.map (a₁.counit.app K)) := by simp [mateEquiv_apply]
  have h₁ := b₂.unit.naturality (T₁.map (β₁.app K))
  have h₂ := θ.naturality (β₁.app K)
  have h₄ := γ₂.naturality (a₁.counit.app K)
  have h₅ := b₂.unit.naturality (γ₁.app (F₁.obj K))
  have h₇ := β₂.naturality (σ.app (F₁.obj K) ≫ H₂.map (a₁.counit.app K))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₄ h₅ h₇
  rw [hmate]
  simp only [CategoryTheory.Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp_assoc T₂, hc, Functor.map_comp_assoc, h₄,
    reassoc_of% hθ]
  simp only [Functor.map_comp]
  rw [← reassoc_of% h₅, reassoc_of% (hu _), hmate']
  simp only [Functor.map_comp, CategoryTheory.Category.assoc] at h₇ ⊢
  rw [← h₇]

private theorem scalar_mate_of_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
    (d : U₂ ⋙ R₁ ≅ R₂ ⋙ U₁) :
    (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
      (((conjugateIsoEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)).symm d).hom))) =
    ((mateEquiv adj₄ adj₃).symm (TwoSquare.mk _ _ _ _ d.hom)) := by
  apply (mateEquiv adj₄ adj₃).injective
  refine NatTrans.ext (funext fun X ↦ ?_)
  have h := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄
    (TwoSquare.mk _ _ _ _
      (((conjugateIsoEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)).symm d).hom))
  rw [Equiv.apply_symm_apply]
  change ((mateEquiv adj₄ adj₃) _).app X = d.hom.app X
  rw [h]
  exact congr_app ((conjugateEquiv (adj₁.comp adj₄)
    (adj₃.comp adj₂)).apply_symm_apply d.hom) X

private theorem inverse_mate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (d : TwoSquare R₁ H G R₂) (M : A) :
    ((mateEquiv adj₁ adj₂).symm d).app M =
      L₂.map (G.map (adj₁.unit.app M)) ≫ L₂.map (d.app (L₁.obj M)) ≫
        adj₂.counit.app (H.obj (L₁.obj M)) := by
  simp [mateEquiv_symm_apply]

private theorem mate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (d : TwoSquare G L₁ L₂ H) (N : B) :
    (mateEquiv adj₁ adj₂ d).app N =
      adj₂.homEquiv _ _ (d.app (R₁.obj N) ≫ H.map (adj₁.counit.app N)) := by
  simp [mateEquiv_apply, Adjunction.homEquiv_apply]

private theorem ordinary_scalar_mate {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    (mateEquiv (sW.normalization.ordinaryAdjunction a.target)
      (sZ.normalization.ordinaryAdjunction a.source)
      (TwoSquare.mk _ _ _ _ (ordinaryBalancing sW sZ a).inv)) =
    proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm := by
  simp only [ordinaryBalancing, Iso.symm_inv]
  rw [scalar_mate_of_conjugate]
  apply NatTrans.ext
  funext M
  change ((mateEquiv
    (proEtaleRingModuleAdjunction q S.target S.source S.identification)
    (proEtaleRingModuleAdjunction q R.target R.source R.identification)).symm
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionDirectImage q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm).hom)).app M = _
  rw [inverse_mate_app]
  rfl

private theorem derived_scalar_mate {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    (mateEquiv (sW.adjunction a.target) (sZ.adjunction a.source)
      (TwoSquare.mk _ _ _ _ (balancing sW sZ a).inv)) =
    (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).inv := by
  simp only [balancing, Iso.symm_inv]
  rw [scalar_mate_of_conjugate]
  apply (mateEquiv (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
    (proEtaleRingDerivedAdjunction q R.target R.source R.identification)).injective
  rw [Equiv.apply_symm_apply]
  refine NatTrans.ext (funext fun N ↦ ?_)
  have h := (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm).2.2
      _ N ((proEtaleRingDerivedAdjunction q S.target S.source S.identification).counit.app N)
  have hc : (proEtaleRingDerivedAdjunction q S.target S.source S.identification).homEquiv
      _ N ((proEtaleRingDerivedAdjunction q S.target S.source S.identification).counit.app N) =
        𝟙 _ :=
    (proEtaleRingDerivedAdjunction q S.target S.source S.identification).right_triangle_components N
  rw [hc, CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp] at h
  change (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm).hom.app N = _
  rw [mate_app]
  exact h.symm

private theorem derived_restriction_pullback_eq {Z W : Scheme.{u}} {q : Z ⟶ W}
    {R S : Coefficients q} (a : CoefficientMap R S)
    [IsIso (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)] :
    (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm).inv =
      (Functor.mapDerivedCategoryCompIso (proEtaleRingRestrictScalars a.target)
          (proEtaleRingModulePullback q R.target R.source R.identification) ≪≫
        Functor.mapDerivedCategoryNatIso (asIso
          (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
            a.target a.source R.identification S.identification a.comm)) ≪≫
        (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback q S.target S.source
          S.identification) (proEtaleRingRestrictScalars a.source)).symm).hom := by
  dsimp [proEtaleRingRestrictionDerivedPullback]
  rw [Category.assoc]
  rfl

/-- The normalized termwise balancing agrees with the conjugate of the actual
restriction/direct-image comparison.
Source: Stacks Project, Tags 03EL, 0D6D, 06YY and 07A6.
(blueprint: lem-sp-finite-free-direct-image-balancing-computed).

Proof: use the tensor-unit normalization to identify the scalar derived
adjunction with the adjunction obtained from the ordinary tensor adjunction.
The identification is checked on flat-term K-flat resolutions, using the recorded
formula for the scalar unit, and extended by the localization universal property.
Invert the displayed counit equation for beta and take its mate under the two
scalar adjunctions. By the normalized scalar unit and counit equations this mate
is computed on homotopy representatives by the ordinary scalar mate, which by
the iterated-mates identity is the inverse-image/restriction comparison of the
ordinary balancing's conjugate square. All four functors of that square are
exact, so its localization satisfies the same factorization equation; cancelling
the exact factorization isomorphisms and using localization extensionality,
the scalar mate of beta inverse is the derived restriction/pullback comparison.
The derived geometric adjunction compatibility shows that the scalar mate of the
inverse canonical balancing is the same comparison. The mate assignment is a
bijection, so beta and balancing have equal inverses and are equal. The
invertibility hypothesis on the source scalar counits is not used. -/
theorem finiteFreeDirectImage_balancingComputed {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S)
    (β : (sW.presentation a.target).derived ⋙
        proEtaleRingDerivedPullback q S.target S.source S.identification ≅
      proEtaleRingDerivedPullback q R.target R.source R.identification ⋙
        (sZ.presentation a.source).derived)
    (hsource : ∀ H : HomotopyCategory (proEtaleRingModules Z R.source) (.up ℤ),
      IsIso ((sZ.presentation a.source).counit.app H))
    (hβ : BalancingComputed sW sZ a β) : β = balancing sW sZ a := by
  have _ := hsource
  let LR := proEtaleRingModulePullback q R.target R.source R.identification
  let LS := proEtaleRingModulePullback q S.target S.source S.identification
  let UW := proEtaleRingRestrictScalars a.target
  let UZ := proEtaleRingRestrictScalars a.source
  let _ := proEtaleRingRestrictionPullbackInv_isIso q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let e := asIso (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm)
  let σ := TwoSquare.mk _ _ _ _
    ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (LR ⋙ (sZ.presentation a.source).ordinary)) (.up ℤ)).hom ≫
      (ordinaryBalancing sW sZ a).inv.mapHomotopyCategory (.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl ((sW.presentation a.target).ordinary ⋙ LS)) (.up ℤ)).inv)
  let θ := TwoSquare.mk _ _ _ _ β.inv
  have hθ (H : HomotopyCategory (proEtaleRingModules W R.target) (.up ℤ)) :
      θ.app (DerivedCategory.Qh.obj H) ≫
        LS.mapDerivedCategory.map ((sW.presentation a.target).counit.app H) ≫
        LS.mapDerivedCategoryFactorsh.hom.app
          (((sW.presentation a.target).ordinary.mapHomotopyCategory (.up ℤ)).obj H) =
      (sZ.presentation a.source).derived.map (LR.mapDerivedCategoryFactorsh.hom.app H) ≫
        (sZ.presentation a.source).counit.app
          ((LR.mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map (σ.app H) := by
    have h := hβ H
    have h := congrArg (fun f ↦ β.inv.app (DerivedCategory.Qh.obj H) ≫ f ≫
      DerivedCategory.Qh.map (σ.app H)) h
    dsimp only [θ, σ, TwoSquare.mk] at h ⊢
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc] at h
    let b₀ : ((sW.presentation a.target).ordinary ⋙ LS).mapHomotopyCategory (.up ℤ) ≅
        (LR ⋙ (sZ.presentation a.source).ordinary).mapHomotopyCategory (.up ℤ) :=
      { hom := (ordinaryBalancing sW sZ a).hom.mapHomotopyCategory (.up ℤ)
        inv := (ordinaryBalancing sW sZ a).inv.mapHomotopyCategory (.up ℤ)
        hom_inv_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
            NatTrans.mapHomotopyCategory_id]
        inv_hom_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
            NatTrans.mapHomotopyCategory_id] }
    let b := Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((sW.presentation a.target).ordinary ⋙ LS)) (.up ℤ) ≪≫
      b₀ ≪≫
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (LR ⋙ (sZ.presentation a.source).ordinary)) (.up ℤ)).symm
    have hi := b.hom_inv_id_app H
    dsimp only [b, b₀, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app] at hi
    simp only [NatTrans.comp_app] at h
    rw [← DerivedCategory.Qh.map_comp] at h
    simp only [Category.assoc] at hi h
    rw [hi] at h
    erw [CategoryTheory.Functor.map_id] at h
    repeat erw [Category.comp_id] at h
    exact h.symm
  have hm : (mateEquiv (sW.adjunction a.target) (sZ.adjunction a.source) θ) =
      (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm).inv := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso (proEtaleRingModules W S.target) (.up ℤ))
    intro K
    have hf := mate_factors
      ((sW.normalization.ordinaryAdjunction a.target).mapHomotopyCategory (.up ℤ))
      ((sZ.normalization.ordinaryAdjunction a.source).mapHomotopyCategory (.up ℤ))
      (sW.adjunction a.target) (sZ.adjunction a.source)
      (sW.presentation a.target).counit UW.mapDerivedCategoryFactorsh.inv
      (sZ.presentation a.source).counit UZ.mapDerivedCategoryFactorsh.inv
      LR.mapDerivedCategoryFactorsh.hom LS.mapDerivedCategoryFactorsh.hom
      (scalar_unit sZ a.source) (scalar_counit sW a.target)
      σ θ K (hθ _)
    have ho := homotopy_mate (sW.normalization.ordinaryAdjunction a.target)
      (sZ.normalization.ordinaryAdjunction a.source) (ordinaryBalancing sW sZ a).symm K
    simp only [Iso.symm_hom] at ho
    rw [ordinary_scalar_mate] at ho
    rw [ho] at hf
    have he := exactSquare_factorsh LS LR UW UZ e K
    have heq : (proEtaleRingRestrictionDerivedPullback q R.target S.target
        R.source S.source a.target a.source R.identification S.identification a.comm).inv =
        (Functor.mapDerivedCategoryCompIso UW LR ≪≫
          Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso LS UZ).symm).hom := by
      exact derived_restriction_pullback_eq a
    rw [← heq] at he
    apply (cancel_epi (LR.mapDerivedCategory.map
      (UW.mapDerivedCategoryFactorsh.inv.app K))).1
    apply (cancel_mono (UZ.mapDerivedCategory.map
      (LS.mapDerivedCategoryFactorsh.hom.app K) ≫
        UZ.mapDerivedCategoryFactorsh.hom.app ((LS.mapHomotopyCategory (.up ℤ)).obj K))).1
    simp only [Category.assoc] at hf he ⊢
    rw [reassoc_of% hf]
    rw [Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [he]
    rw [← LR.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    repeat erw [Category.id_comp]
  have hi : β.inv = (balancing sW sZ a).inv := by
    suffices TwoSquare.mk _ _ _ _ β.inv =
        TwoSquare.mk _ _ _ _ (balancing sW sZ a).inv from this
    apply (mateEquiv (sW.adjunction a.target) (sZ.adjunction a.source)).injective
    refine NatTrans.ext (funext fun X ↦ ?_)
    exact congr_app (hm.trans (derived_scalar_mate sW sZ a).symm) X
  have h := congrArg Iso.symm (Iso.ext hi : β.symm = (balancing sW sZ a).symm)
  exact h

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
