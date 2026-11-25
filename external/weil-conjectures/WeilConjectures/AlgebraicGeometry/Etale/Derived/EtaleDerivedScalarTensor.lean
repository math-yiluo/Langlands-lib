/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange

import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-!
# Ordinary derived scalar extension in the constant-coefficient presentation

Source: Stacks Project, Tags 03EK and 06YY
(blueprint: lem-pur-derived-change-of-rings).
The general ring-sheaf interface is reexported. The additional interface uses
ModuleCat-valued sheaves and fixes the scalar/tensor comparison on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w v₁ v₂ w₁ w₂ c₁ c₂ h₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Additivity of the existing sheafified sectionwise scalar extension.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings).
Proof: its adjunction to additive restriction implies additivity. -/
@[instance] theorem scalarSheafExtension_additive
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).Additive := by
  exact (ProEtale.etaleSheafExtendScalarsAdjunction φ T).left_adjoint_additive

/-- The published scalar-extension functor in the small-etale specialization.
This is an abbreviation for the existing chosen left adjoint, not a new construction.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
abbrev scalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ

/-- B as an A-module sheaf, using actual exact restriction of scalars.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings). -/
def scalarCoefficientSheaf
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
    (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)))

/-- B_T[0], with its restricted A-action.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : DerivedCategoryModule A T :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj (scalarCoefficientSheaf φ T)

/-- The ordinary balancing map M tensor_A B to the restricted scalar extension.
It is scalar unit, followed by the lax tensorator of restriction and the right unitor.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings). -/
def scalarSheafTensorMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    M ⊗ scalarCoefficientSheaf φ T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        ((ProEtale.etaleSheafExtendScalars φ T).obj M) :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M ▷
      scalarCoefficientSheaf φ T ≫
    Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ)
      ((ProEtale.etaleSheafExtendScalars φ T).obj M) (𝟙_ _) ≫
    (Sheaf.restrictScalars T.smallEtaleTopology φ).map (ρ_ _).hom

private theorem balancing_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxMonoidal] (adj : L ⊣ R)
    {M N : C} (a : M ⟶ N) :
    a ▷ R.obj (𝟙_ D) ≫
        (adj.unit.app N ▷ R.obj (𝟙_ D) ≫
          Functor.LaxMonoidal.μ R (L.obj N) (𝟙_ D) ≫ R.map (ρ_ (L.obj N)).hom) =
      (adj.unit.app M ▷ R.obj (𝟙_ D) ≫
          Functor.LaxMonoidal.μ R (L.obj M) (𝟙_ D) ≫ R.map (ρ_ (L.obj M)).hom) ≫
        R.map (L.map a) := by
  have hn : a ≫ adj.unit.app N = adj.unit.app M ≫ R.map (L.map a) :=
    adj.unit.naturality a
  rw [← comp_whiskerRight_assoc, hn]
  rw [comp_whiskerRight_assoc, Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [← R.map_comp, rightUnitor_naturality, R.map_comp]
  simp only [Category.assoc]

/-- Naturality of the balancing map.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings).
Proof: apply naturality of the scalar unit, the lax tensorator, and the right unitor.
On sections this is (m tensor b) maps to b tensor a(m). -/
theorem scalarSheafTensorMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (a : M ⟶ N) :
    a ▷ scalarCoefficientSheaf φ T ≫ scalarSheafTensorMap φ T N =
      scalarSheafTensorMap φ T M ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map
          ((ProEtale.etaleSheafExtendScalars φ T).map a) := by
  exact balancing_naturality (ProEtale.etaleSheafExtendScalarsAdjunction φ T) a

/-- The ordinary balancing map, as a natural transformation.
Source: Stacks 03EK (blueprint: lem-pur-derived-change-of-rings). -/
def scalarSheafTensorTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    tensorRight (scalarCoefficientSheaf φ T) ⟶
      ProEtale.etaleSheafExtendScalars φ T ⋙ Sheaf.restrictScalars T.smallEtaleTopology φ where
  app := scalarSheafTensorMap φ T
  naturality _ _ a := scalarSheafTensorMap_naturality φ T a

section Representative

variable {C : Type v} {D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (adj : F ⊣ R) (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
  (ad : E ⊣ R.mapDerivedCategory)

/-- The cochain adjunction transpose, sharing ordinary and derived functor endpoints.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
abbrev scalarAdjunctionRepresentativeMap (P : CochainComplex C ℤ) :
    E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  (ad.homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).inv.app P) ≫
      R.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P))

end Representative

/-- The ordinary scalar unit on a cochain representative.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def scalarRepresentativeUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    P ⟶ ((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
    (NatTrans.mapHomologicalComplex
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
        Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).inv.app P

/-- The derived-extension counit on a cochain representative, including the quotient factor.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
              Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P))

/-- The scalar representative has the specified scalar-unit transpose.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings).
Proof: apply the Hom equivalence to its inverse in the definition of the
representative. -/
theorem scalarExtensionRepresentative_unit_public
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app
        (_root_.DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        (scalarExtensionRepresentative φ T P) =
    _root_.DerivedCategory.Q.map (scalarRepresentativeUnit φ T P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv _ _).apply_symm_apply _

/-- Exact restriction of the scalar-extension representative map.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarRestrictedExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).obj
        ((scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P)) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ T ⋙
          Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
      (scalarExtensionRepresentative φ T P) ≫
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.hom.app
      (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
          Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).hom.app P)

/-- Tensoring with F[0], in the general monoidal-category interface.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarTensorModelFunctor
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (F : C) : _root_.DerivedCategory C ⥤ _root_.DerivedCategory C :=
  tensorRight ((_root_.DerivedCategory.singleFunctor C 0).obj F)

/-- Normalization by the ordinary balancing map on cochain representatives.
This general helper shares the monoidal data with the tensor-model API before specialization.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarTensorModelNormalization
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (F : C) {V : C ⥤ C} [V.Additive]
    (τ : tensorRight F ⟶ V) {G : _root_.DerivedCategory C ⥤ _root_.DerivedCategory C}
    (e : G ≅ scalarTensorModelFunctor F)
    (r : ∀ P : CochainComplex C ℤ,
      G.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P)) : Prop :=
  ∀ P : CochainComplex C ℤ,
    e.hom.app (_root_.DerivedCategory.Q.obj P) ≫
        Functor.LaxMonoidal.μ (_root_.DerivedCategory.Q (C := C)) P
          ((HomologicalComplex.single C (.up ℤ) 0).obj F) ≫
        _root_.DerivedCategory.Q.map
          ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) F).hom.app P) ≫
        _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) = r P

private theorem tensor_model_eq
    (D : Type w) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology D) :
    (derivedTensor D T).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) =
      scalarTensorModelFunctor F := by
  rfl

/-- The site-specific tensor and the general tensor-model functor have the same data.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings).
Proof: unfold derivedTensor, scalarCoefficient and scalarTensorModelFunctor.
Both sides are curriedTensor on the same derived monoidal structure, with its
second argument the restricted B-unit sheaf in degree zero. -/
theorem scalarTensorFunctor_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (scalarCoefficient φ T) =
      scalarTensorModelFunctor (scalarCoefficientSheaf φ T) := by
  exact tensor_model_eq (ModuleCat.{u + 1} A) T (scalarCoefficientSheaf φ T)

-- Stacks 06YU/06XN: the tensor counit and the chosen-adjoint counit derive the same functor.
-- These generic calculations follow the private comparison proof in SupportedEtaleTensorOrigin.
section TensorComparison

variable {C : Type c₁} [Category.{h₁} C] [Abelian C] [IsGrothendieckAbelian.{h₁} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{h₁} C] [Abelian.HasFunctorialFlatResolution C]

private def tensorCounit (F : C) :
    DerivedCategory.Q ⋙ scalarTensorModelFunctor F ⟶
      (tensorRight F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((HomologicalComplex.single C (.up ℤ) 0).obj F) ≫
    DerivedCategory.Q.map
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) F).hom.app P)
  naturality P R a := by
    change (DerivedCategory.Q.map a ▷ _) ≫ _ = _
    erw [Functor.LaxMonoidal.μ_natural_left_assoc]
    erw [← DerivedCategory.Q.map_comp]
    erw [(CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (curriedTensor C) F).hom.naturality a]
    erw [DerivedCategory.Q.map_comp]
    simp only [Functor.comp_map, Category.assoc]

private theorem tensorCounit_isIso (F : C) (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso ((tensorCounit F).app P) := by
  have h : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F))) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj F))
    ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((HomologicalComplex.single C (.up ℤ) 0).obj F)) := by
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) P
          ((HomologicalComplex.single C (.up ℤ) 0).obj F))) ≫ _)
    infer_instance
  dsimp only [tensorCounit]
  infer_instance

private theorem tensorComparison_existsUnique (F : C) (V : C ⥤ C) [V.Additive]
    (τ : tensorRight F ≅ V) (G : DerivedCategory C ⥤ DerivedCategory C)
    (r : DerivedCategory.Q ⋙ G ⟶ V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hr : ∀ P : CochainComplex C ℤ,
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P → IsIso (r.app P))
    (r₀ : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj P))
    (hrr : ∀ P, r.app P = r₀ P) :
    ∃! e : G ≅ scalarTensorModelFunctor F,
      scalarTensorModelNormalization F τ.hom e r₀ := by
  let α := tensorCounit F ≫ Functor.whiskerRight
    (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)) DerivedCategory.Q
  have hα : (scalarTensorModelFunctor F).IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
    apply (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_of_isLeftDerivabilityStructure α
    intro P
    change IsIso (α.app P.obj)
    have := tensorCounit_isIso F P.obj P.property
    have : IsIso ((NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app P.obj) :=
      ((NatIso.mapHomologicalComplex τ (.up ℤ)).app P.obj).isIso_hom
    dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have hG : G.IsLeftDerivedFunctor r (HomologicalComplex.quasiIso C (.up ℤ)) := by
    apply (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_of_isLeftDerivabilityStructure r
    exact fun P ↦ hr P.obj P.property
  let e : G ≅ scalarTensorModelFunctor F :=
    Functor.leftDerivedUnique _ _ r α (HomologicalComplex.quasiIso C (.up ℤ))
  have he : scalarTensorModelNormalization F τ.hom e r.app := by
    intro P
    simpa only [e, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom, Iso.refl_hom,
      α, tensorCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      NatTrans.id_app, Category.comp_id, Category.assoc] using
      (Functor.leftDerivedNatTrans_app _ _ r α
        (HomologicalComplex.quasiIso C (.up ℤ)) (𝟙 _) P)
  refine ⟨e, fun P ↦ (he P).trans (hrr P), ?_⟩
  intro e' he'
  apply Iso.ext
  apply Functor.leftDerived_ext _ α (HomologicalComplex.quasiIso C (.up ℤ))
  ext P
  simpa only [α, tensorCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using ((he' P).trans (hrr P).symm).trans (he P).symm

private theorem adjointTensorComparison
    {D : Type c₂} [Category.{h₁} D] [Abelian D] [HasDerivedCategory.{h₁} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
    (ad : L ⊣ U.mapDerivedCategory) (F : C) (τ : tensorRight F ≅ E ⋙ U)
    (r₀ : ∀ P : CochainComplex C ℤ,
      (L ⋙ U.mapDerivedCategory).obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj (((E ⋙ U).mapHomologicalComplex (.up ℤ)).obj P))
    (hr₀ : ∀ P, r₀ P = U.mapDerivedCategory.map
        ((ad.homEquiv _ _).symm
          (DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
                (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
                (Functor.mapHomologicalComplexCompIso
                  (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
            U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).hom.app P)) :
    ∃! e : L ⋙ U.mapDerivedCategory ≅ scalarTensorModelFunctor F,
      scalarTensorModelNormalization F τ.hom e r₀ := by
  let η : DerivedCategory.Q ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ U.mapDerivedCategory :=
    { app P := DerivedCategory.Q.map
          (((adj).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P)
      naturality P R a := by
        have hn := ((adj).mapHomologicalComplex
          (.up ℤ)).unit.naturality a
        change a ≫ _ = _ at hn
        rw [← DerivedCategory.Q.map_comp_assoc, hn]
        rw [DerivedCategory.Q.map_comp, Category.assoc]
        simpa only [Functor.comp_map, Category.assoc] using congrArg
          (fun b ↦ DerivedCategory.Q.map
            (((adj).mapHomologicalComplex
              (.up ℤ)).unit.app P) ≫ b)
          (U.mapDerivedCategoryFactors.inv.naturality
            ((E.mapHomologicalComplex (.up ℤ)).map a)) }
  let r : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    { app P := (ad.homEquiv _ _).symm (η.app P)
      naturality P R a := ad.homEquiv_naturality_right_square
        (DerivedCategory.Q.map a) (η.app R) (η.app P)
        (DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map a)) (η.naturality a) }
  have hr (P : CochainComplex C ℤ)
      (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) : IsIso (r.app P) := by
    exact Adjunction.isIso_cochainTranspose_of_kFlat E U
      (adj) ad P hP
  let r' : DerivedCategory.Q ⋙ (L ⋙ U.mapDerivedCategory) ⟶
      (E ⋙ U).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight r U.mapDerivedCategory ≫
      Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ)) U.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).hom
        DerivedCategory.Q
  have hr' (P : CochainComplex C ℤ)
      (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) : IsIso (r'.app P) := by
    have := hr P hP
    dsimp only [r', NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hrep (P : CochainComplex C ℤ) : r'.app P = r₀ P := by
    dsimp only [r', r, η, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    have hu : (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
        (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
      ext i
      simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
        NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
        Iso.refl_inv, NatTrans.id_app, Category.id_comp]
      change adj.unit.app (P.X i) = adj.unit.app (P.X i) ≫ 𝟙 _
      exact (Category.comp_id _).symm
    rw [hu]
    exact (hr₀ P).symm
  exact tensorComparison_existsUnique F (E ⋙ U) τ (L ⋙ U.mapDerivedCategory) r' hr' r₀ hrep

end TensorComparison

section ScalarSpecialization

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem scalarBalancing_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (scalarSheafTensorMap φ T M) := by
  let := φ.toAlgebra
  have : T.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  exact isIso_sheafAdjunction_unitProjection T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap A B)) M

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem scalarExtension_preservesKFlatQuasiIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  have : IsIso (scalarSheafTensorTransformation φ T) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact scalarBalancing_isIso φ T
  let τ := asIso (scalarSheafTensorTransformation φ T)
  apply Functor.PreservesKFlatQuasiIso.mk'
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa
    (scalarCoefficientSheaf φ T)
  have he : (((E ⋙ U).mapHomologicalComplex _).obj K).Acyclic :=
    ht.of_iso ((NatIso.mapHomologicalComplex τ _).app K)
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (he n)

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
/-- The scalar/tensor comparison is uniquely fixed on K-flat representatives.
Source: Stacks 06YY, using 03EK (blueprint: lem-pur-derived-change-of-rings).
Proof: the ordinary balancing map sends m tensor b to b tensor m and is an
isomorphism after sheafification. Apply it termwise to a K-flat resolution P.
The left-derived counit computes scalar extension on P. The canonical lax tensorator
of Q, followed by the total-tensor/single-complex comparison, is the tensor-model
isomorphism on K-flat P. Exact restriction
commutes with Q. These maps yield the displayed normalized isomorphism. For a
quasi-isomorphism between K-flat resolutions all maps commute by naturality, so
localization gives a natural isomorphism independent of the resolution. Naturality
with respect to a K-flat resolution gives the normalization on every complex. Every
object has such a resolution; the same equations determine every component,
which proves uniqueness of the natural isomorphism. -/
theorem scalarTensorIso_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ∃! e : scalarExtension φ T ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ≅
        (derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (scalarCoefficient φ T),
      scalarTensorModelNormalization (scalarCoefficientSheaf φ T)
        (scalarSheafTensorTransformation φ T)
        (e ≪≫ eqToIso (scalarTensorFunctor_eq φ T))
        (scalarRestrictedExtensionRepresentative φ T) := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  have : E.PreservesKFlatQuasiIso := scalarExtension_preservesKFlatQuasiIso φ T
  have : PreservesFiniteLimits U := by
    let := (ProEtale.etaleSheafExtendScalarsAdjunction φ T).rightAdjoint_preservesLimits
    infer_instance
  have : PreservesFiniteColimits U := by
    let := (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).leftAdjoint_preservesColimits
    infer_instance
  have : IsIso (scalarSheafTensorTransformation φ T) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact scalarBalancing_isIso φ T
  obtain ⟨e, he, hue⟩ := adjointTensorComparison E U
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T) (scalarExtension φ T)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (scalarCoefficientSheaf φ T) (asIso (scalarSheafTensorTransformation φ T))
    (scalarRestrictedExtensionRepresentative φ T) (fun _ ↦ rfl)
  let e₀ := eqToIso (scalarTensorFunctor_eq φ T)
  refine ⟨e ≪≫ e₀.symm, ?_, ?_⟩
  · simpa only [e₀, asIso_hom, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using he
  · intro e' he'
    have h := hue (e' ≪≫ e₀) he'
    have hh := congrArg (fun i ↦ i ≪≫ e₀.symm) h
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hh

end ScalarSpecialization

/-- Canonical scalar/tensor identification; its defining theorem determines it uniquely.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def scalarTensorIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarExtension φ T ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ≅
      (derivedTensor (ModuleCat.{u + 1} A) T).flip.obj (scalarCoefficient φ T) :=
  (scalarTensorIso_existsUnique φ T).choose

end AlgebraicGeometry.Etale
