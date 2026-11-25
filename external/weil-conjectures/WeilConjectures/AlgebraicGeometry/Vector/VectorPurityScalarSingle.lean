/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoUniqueness
import all Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Degree-zero scalar comparisons for vector purity

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-scalar-single).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The ordinary sheafified scalar extension and its actual adjunction.
Source: Stacks 03EK (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarSheaf {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  ProEtale.etaleSheafExtendScalars φ T

/-- The ordinary scalar extension adjunction from the published sectionwise tensor.
Source: Stacks 03EK (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarSheafAdjunction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    purityScalarSheaf φ T ⊣ Sheaf.restrictScalars T.smallEtaleTopology φ :=
  ProEtale.etaleSheafExtendScalarsAdjunction φ T

/-- The universal derived scalar tensor, reusing the landed constant-ring adjunction.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension φ T

/-- The published scalar/pullback comparison, in the orientation used by reduction.
Source: Stacks 07A4 (blueprint: def-pur-vector-purity-scalar-single). -/
abbrev purityScalarPullback {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(upperStar (ModuleCat.{u + 1} A) f) ⋙ purityScalarExtension φ X ≅
      purityScalarExtension φ Y ⋙ L(upperStar (ModuleCat.{u + 1} B) f) :=
  (scalarPullbackIso φ f).symm

/-- The specified derived scalar adjunction, obtained from the landed right-adjoint instance.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarAdjunction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    purityScalarExtension φ T ⊣
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ :=
  Adjunction.ofIsRightAdjoint _

/-- Component of the published representative-normalized scalar tensor comparison.
Source: Stacks 07A4, `ExceptionalCoefficients.tensorIso`
(blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarTensor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (K L : DerivedCategoryModule A T) :
    (purityScalarExtension φ T).obj (K ⊗ L) ≅
      (purityScalarExtension φ T).obj K ⊗ (purityScalarExtension φ T).obj L :=
  (ExceptionalCoefficients.tensorIso φ T).app (K, L)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Factor the scalar/single adjunction transpose in abstract categories, sharing its
functor endpoints before specializing to coefficient sheaves. This is the same unit
and exact-single comparison used below, with no extra choice of comparison.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def purityAdjunctionSingleMap
    {C : Type v₁} {D : Type v₂} {E : Type v₃} {F : Type v₄}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E] [Category.{w₄} F]
    (S : C ⥤ D) (R : D ⥤ C) (Q : E ⥤ F) (V : F ⥤ E)
    (i : C ⥤ E) (j : D ⥤ F) (a : S ⊣ R) (b : Q ⊣ V)
    (c : j ⋙ V ≅ R ⋙ i) (M : C) : Q.obj (i.obj M) ⟶ j.obj (S.obj M) :=
  (b.homEquiv _ _).symm (i.map (a.unit.app M) ≫ c.inv.app (S.obj M))

/-- Transport a scalar-unit arrow along the specified single/unit identifications.
The generic endpoints keep kernel checking from expanding the derived monoidal data.
Source: proposition-purity-vector-bundles, Step 6 (blueprint:
def-pur-vector-purity-scalar-single). -/
def purityTransportUnitMap {C : Type v₁} {D : Type v₂}
    [Category.{w₁} C] [Category.{w₂} D] (Q : C ⥤ D)
    {U U' : C} {V V' : D} (e : U ≅ U') (f : V ≅ V')
    (m : Q.obj U ⟶ V) : Q.obj U' ⟶ V' :=
  Q.map e.inv ≫ m ≫ f.hom

/-- Form a single-object comparison from a cochain representative transformation.
The single/quotient comparisons on both sides are the existing canonical ones.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def puritySingleFromRepresentativeMap
    {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₃} C] [HasDerivedCategory.{w₄} D]
    (F : C ⥤ D) [F.Additive] (E : DerivedCategory C ⥤ DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) (M : C) :
    E.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj (F.obj M) :=
  E.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app M) ≫
    rep ((CochainComplex.singleFunctor C 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ D 0).inv.app (F.obj M)

section RepresentativeSingle

variable {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₃} C] [HasDerivedCategory.{w₄} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (adj : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
  (ad : L ⊣ U.mapDerivedCategory)

/-- The representative scalar/single arrow, sharing its ordinary and derived adjunctions.
This is the localized cochain-unit formula, with the single/quotient comparisons on both sides.
Source: Stacks 06YY and 07A6 (blueprint: def-pur-vector-purity-scalar-single). -/
def purityRepresentativeSingleMap (M : C) :
    L.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj (E.obj M) :=
    puritySingleFromRepresentativeMap E L
    (Etale.scalarAdjunctionRepresentativeMap E U adj L ad) M

end RepresentativeSingle

end AlgebraicGeometry.Etale

namespace CategoryTheory
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (adj : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
  (ad : L ⊣ U.mapDerivedCategory)
set_option linter.flexible false in
private theorem single_adjunction_formula (M : C) :
    (ad.homEquiv _ _).symm
      ((DerivedCategory.singleFunctor _ 0).map (adj.unit.app M) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj M)) =
    (ad.homEquiv _ _).symm
      (DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app
          ((CochainComplex.singleFunctor C 0).obj M)) ≫
        U.mapDerivedCategoryFactors.inv.app
          ((E.mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj M))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) := by
  rw [← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((CochainComplex.singleFunctor D 0).obj (E.obj M)))).1
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  have hn := U.mapDerivedCategoryFactors.hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [hn, Iso.inv_hom_id_app_assoc]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq]
    change adj.unit.app M ≫ (𝟙 _ ≫ U.map (𝟙 _)) = adj.unit.app M ≫ U.map (𝟙 _)
    rw [Category.id_comp]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _

/-- The adjunction and representative single comparisons agree.
Source: Stacks 06YY, 07A6 (blueprint: def-pur-vector-purity-scalar-single). -/
theorem purityAdjunctionSingleMap_eq_representative (M : C) :
    AlgebraicGeometry.Etale.purityAdjunctionSingleMap E U L U.mapDerivedCategory
      (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor D 0)
      adj ad (U.mapDerivedCategorySingleFunctor 0) M =
    AlgebraicGeometry.Etale.purityRepresentativeSingleMap E U adj L ad M := by
  unfold AlgebraicGeometry.Etale.purityRepresentativeSingleMap
    AlgebraicGeometry.Etale.puritySingleFromRepresentativeMap
    Etale.scalarAdjunctionRepresentativeMap
  rw [← AlgebraicGeometry.Etale.mapComplex_unit_formula]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [L.map_id, Category.id_comp, Category.comp_id]
  exact single_adjunction_formula E U adj L ad M
end CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The comparison on a sheaf in degree zero is the scalar transpose of the ordinary
scalar-unit map, followed by the exact restriction/single comparison.
Source: Stacks 06YY (blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarSingleMap {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Etale.purityScalarExtension φ T).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((Etale.purityScalarSheaf φ T).obj M) :=
  purityAdjunctionSingleMap (Etale.purityScalarSheaf φ T)
    (Sheaf.restrictScalars T.smallEtaleTopology φ) (Etale.purityScalarExtension φ T)
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (Etale.purityScalarSheafAdjunction φ T) (Etale.purityScalarAdjunction φ T)
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0) M

/-- The scalar image of the degree-zero coefficient unit, given by the published
normalized scalar unit identification `ExceptionalCoefficients.unitIso` (uniquely
fixed by the ordinary multiplication B tensor_A A -> B on the K-flat unit complex),
transported along both single/unit identifications.
Source: proposition-purity-vector-bundles, unit normalization in Step 6; Stacks 07A4
(blueprint: def-pur-vector-purity-scalar-single). -/
def purityScalarUnitMap {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (T : Scheme.{u}) :
    (Etale.purityScalarExtension φ T).obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) :=
  purityTransportUnitMap (Etale.purityScalarExtension φ T)
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).symm
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A') T).symm
    (Etale.ExceptionalCoefficients.unitIso φ T).hom

end AlgebraicGeometry.Etale
