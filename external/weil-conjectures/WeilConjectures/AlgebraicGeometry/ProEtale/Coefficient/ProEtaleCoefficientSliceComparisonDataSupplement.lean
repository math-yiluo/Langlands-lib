/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarExtensionSliceComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientSliceComparisonData

/-! # Closed slice comparison with transported pro-etale coefficients

Comparison data and their defining section and representative equations.

## References

* Hemo--Richarz--Scholbach, Lemma 4.5, and Stacks Project, Tags 03CE, 03EL, 07A4, 08J7, 08J9, 08JB
  and 0FPT
* Stacks 03CZ, 03CY and 07A4
* Stacks 06YN, 07A4
* Stacks 03CE and 05RT
* Hemo--Richarz--Scholbach Lemma 4.5

## Implementation details

The normalization equations `Normalized` are kept out of the data record `Data` so that Lean
does not expand them in every generated projection and constructor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true in
/-- Sectionwise restriction is additive and exact on the small pro-etale sites. -/
theorem proEtaleSliceModuleRestriction_exact {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleSliceModuleRestriction U O).Additive ∧
      PreservesFiniteLimits (proEtaleSliceModuleRestriction U O) ∧
      PreservesFiniteColimits (proEtaleSliceModuleRestriction U O) := by
  exact proEtaleSliceModules_exact U O

/-- Ordinary derived restriction; its construction is exact termwise localization. -/
def proEtaleSliceDerivedRestriction {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  haveI := (proEtaleSliceModuleRestriction_exact U O).1
  haveI := (proEtaleSliceModuleRestriction_exact U O).2.1
  haveI := (proEtaleSliceModuleRestriction_exact U O).2.2
  (proEtaleSliceModuleRestriction U O).mapDerivedCategory

/-- Scalar transport on ordinary unbounded derived categories, by exact termwise descent. -/
def proEtaleSliceDerivedScalarTransport {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (b : proEtaleSliceRing U O ≅ B) :=
  (proEtaleSliceScalarTransport U O B b).mapDerivedCategory

/-- The closed comparison is the transpose of transported evaluation, with the inverse
of the specified tensor comparison. It therefore fixes its normalization uniquely. -/
def coefficientClosedPullbackMap
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {H : Dᵒᵖ × D ⥤ D} {HB : Eᵒᵖ × E ⥤ E}
    (S : CoefficientClosedStructure H) (SB : CoefficientClosedStructure HB)
    (F : D ⥤ E) (rho : S.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (L M : D) :
    F.obj (H.obj (op L, M)) ⟶ HB.obj (op (F.obj L), F.obj M) :=
  SB.transpose _ _ _ ((rho.app (H.obj (op L, M), L)).inv ≫ F.map (S.evaluation L M))

/-- Inclusion of the existing flat representatives into all K-flat representatives. -/
def proEtaleFlatToKFlat (X : Scheme.{u})
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ObjectProperty.ιOfLE (P := proEtaleFlatRepresentatives X O)
    (P' := CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := O))
    (fun P hP ↦ (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP.1)

/-- Restrict the tensor presentation to the flat representatives. -/
def proEtaleClosedTensorModel (X : Scheme.{u})
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
    (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S) :
    ProEtaleTensorModel X O where
  tensor := S.tensor
  representative := Functor.isoWhiskerLeft
    ((proEtaleFlatToKFlat X O).prod (proEtaleFlatToKFlat X O)) T.comparison

/-- Additivity of the sectionwise restriction used by this comparison. -/
instance proEtaleSliceRestriction_additive {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleSliceModuleRestriction U O).Additive :=
  (proEtaleSliceModuleRestriction_exact U O).1

/-- Finite-limit preservation of sectionwise restriction. -/
instance proEtaleSliceRestriction_limits {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleSliceModuleRestriction U O) :=
  (proEtaleSliceModuleRestriction_exact U O).2.1

/-- Finite-colimit preservation of sectionwise restriction. -/
instance proEtaleSliceRestriction_colimits {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleSliceModuleRestriction U O) :=
  (proEtaleSliceModuleRestriction_exact U O).2.2
/-- Exact localization of the normalized ordinary comparison, with its canonical
composition comparison. -/
def proEtaleSliceDerivedComparison {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})
    (a : proEtaleRingModulePullback U.hom O B c ≅
      proEtaleSliceModuleRestriction U O ⋙ proEtaleSliceScalarTransport U O B
        (proEtaleSliceCoefficientIso U O B c delta)) :
    proEtaleRingDerivedPullback U.hom O B c ≅
      proEtaleSliceDerivedRestriction U O ⋙ proEtaleSliceDerivedScalarTransport U O B
        (proEtaleSliceCoefficientIso U O B c delta) :=
  Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm


/-- The exact termwise functor used in the representative normalizations. -/
abbrev proEtaleComparisonComplex {X Y : Scheme.{u}}
    {O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (K : proEtaleRingModules X O ⥤ proEtaleRingModules Y B) [K.Additive] :=
  K.mapHomologicalComplex (.up ℤ)

attribute [local irreducible] CoefficientTensorModels.iso

/-- The exact tensor localization square, kept separate to avoid expanding it in
structure projections. -/
def ProEtaleSliceTensorModel {X Y : Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (K : proEtaleRingModules X O ⥤ proEtaleRingModules Y B)
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
    (SB : CoefficientClosedStructure (proEtaleCoefficientHom Y B))
    (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
    (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology Y) B SB)
    (chain : ∀ P Q : CochainComplex (proEtaleRingModules X O) ℤ,
      (proEtaleComparisonComplex K).obj
          ((coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) O).obj (P, Q)) ≅
        (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) B).obj
          ((proEtaleComparisonComplex K).obj P, (proEtaleComparisonComplex K).obj Q))
    (kflat : ∀ P : CochainComplex (proEtaleRingModules X O) ℤ,
      P.IsKFlatIndependentCoefficients →
        CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := B)
          ((proEtaleComparisonComplex K).obj P))
    (rho : S.tensor ⋙ K.mapDerivedCategory ≅
      (K.mapDerivedCategory.prod K.mapDerivedCategory) ⋙ SB.tensor) : Prop :=
  ∀ (P Q : CochainComplex (proEtaleRingModules X O) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
    K.mapDerivedCategory.map (T.iso (ProEt.topology X) O S P Q hP hQ).hom ≫
        rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SB.tensor.map (Prod.mkHom (K.mapDerivedCategoryFactors.hom.app P)
          (K.mapDerivedCategoryFactors.hom.app Q)) =
      K.mapDerivedCategoryFactors.hom.app
        ((coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) O).obj (P, Q)) ≫
        DerivedCategory.Q.map (chain P Q).hom ≫
        (TB.iso (ProEt.topology Y) B SB _ _ (kflat P hP) (kflat Q hQ)).hom

/-- A tensor comparison together with the chain-level comparison `chain` and its exact
localization square. -/
structure ProEtaleSliceTensorDescent {X Y : Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (K : proEtaleRingModules X O ⥤ proEtaleRingModules Y B)
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
    (SB : CoefficientClosedStructure (proEtaleCoefficientHom Y B))
    (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
    (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology Y) B SB) where
  /-- The canonical chain comparison, to be normalized on pure summands below. -/
  chain : ∀ P Q : CochainComplex (proEtaleRingModules X O) ℤ,
    (proEtaleComparisonComplex K).obj
        ((coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) O).obj (P, Q)) ≅
      (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) B).obj
        ((proEtaleComparisonComplex K).obj P, (proEtaleComparisonComplex K).obj Q)
  /-- Exact termwise restriction and scalar transport preserve K-flatness. -/
  kflat : ∀ P : CochainComplex (proEtaleRingModules X O) ℤ,
    P.IsKFlatIndependentCoefficients →
      CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := B)
        ((proEtaleComparisonComplex K).obj P)
  /-- The derived tensor comparison is natural in both inputs. -/
  rho : S.tensor ⋙ K.mapDerivedCategory ≅
    (K.mapDerivedCategory.prod K.mapDerivedCategory) ⋙ SB.tensor
  /-- Its value is the specified exact localization square. -/
  model : ProEtaleSliceTensorModel O B K S SB T TB chain kflat rho

/-- The ordinary coefficient module; this abbreviates the tensor unit. -/
abbrev proEtaleCoefficientUnit (X : Scheme.{u})
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.unit ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)

/-- Degree-zero localization of the ordinary unit comparison. Conjugating with the
`RingedDerivedTensorCoherence.unitIso` gives the derived tensor-unit map. -/
def proEtaleDerivedCoefficientUnit {X Y : Scheme.{u}}
    {O : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (K : proEtaleRingModules X O ⥤ proEtaleRingModules Y B)
    [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (e : K.obj (proEtaleCoefficientUnit X O) ≅ proEtaleCoefficientUnit Y B) :=
  (K.mapDerivedCategorySingleFunctor 0).app (proEtaleCoefficientUnit X O) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

namespace ProEtaleCoefficientSliceComparison

variable {X : Scheme.{u}} (U : X.ProEt)
  (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
  (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})

/-- Exact slice restriction on the canonically equivalent source site. -/
abbrev r := proEtaleSliceModuleRestriction U O

/-- Additivity of the exact slice restriction presentation. -/
instance r_additive : (r U O).Additive := proEtaleSliceRestriction_additive U O

/-- Exactness on kernels of the slice restriction presentation. -/
instance r_limits : PreservesFiniteLimits (r U O) := proEtaleSliceRestriction_limits U O

/-- Exactness on cokernels of the slice restriction presentation. -/
instance r_colimits : PreservesFiniteColimits (r U O) := proEtaleSliceRestriction_colimits U O

variable (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
  (SR : CoefficientClosedStructure (proEtaleCoefficientHom U.left (proEtaleSliceRing U O)))
  (SB : CoefficientClosedStructure (proEtaleCoefficientHom U.left B))
  (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
  (TR : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left)
    (proEtaleSliceRing U O) SR)
  (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left) B SB)

/-- The canonical pullback tensor comparison on the fixed closed tensor presentations. -/
abbrev rho := proEtaleCanonicalTensorComparison U.hom O B c
  (proEtaleClosedTensorModel X O S T) (proEtaleClosedTensorModel U.left B SB TB)

/-- The normalized comparison assertions, including scalar transport, tensor, unit,
internal Hom, evaluation, transpose and symmetry. All existential comparison data
are pinned down by the displayed section or representative formulas. -/
structure Data where
  /-- Delta on module inverse image, with the scalar action transported by b. -/
  ordinary : f U O B c ≅ r U O ⋙ e U O B c delta
  /-- Exact normalized tensor descent for restriction. -/
  restrictionTensor : @ProEtaleSliceTensorDescent X U.left O (proEtaleSliceRing U O)
    (r U O) (r_additive U O) (r_limits U O) (r_colimits U O) S SR T TR
  /-- Exact normalized tensor descent for scalar transport. -/
  scalarTensor : ProEtaleSliceTensorDescent (proEtaleSliceRing U O) B
    (e U O B c delta) SR SB TR TB
  /-- The canonical ordinary restriction unit. -/
  restrictionUnit : (r U O).obj (proEtaleCoefficientUnit X O) ≅
    proEtaleCoefficientUnit U.left (proEtaleSliceRing U O)
  /-- The scalar unit sends a to b(a). -/
  scalarUnit : (e U O B c delta).obj
    (proEtaleCoefficientUnit U.left (proEtaleSliceRing U O)) ≅ proEtaleCoefficientUnit U.left B
  /-- The pullback unit, retaining the prescribed coefficient structure map. -/
  pullbackUnit : (f U O B c).obj (proEtaleCoefficientUnit X O) ≅
    proEtaleCoefficientUnit U.left B
  /-- The natural canonical slice Hom comparison. -/
  restrictionHom : proEtaleCoefficientHom X O ⋙ (r U O).mapDerivedCategory ≅
    ((r U O).mapDerivedCategory.op.prod (r U O).mapDerivedCategory) ⋙
      proEtaleCoefficientHom U.left (proEtaleSliceRing U O)
  /-- The scalar Hom comparison is the identity on local linear-map families. -/
  scalarHom : proEtaleCoefficientHom U.left (proEtaleSliceRing U O) ⋙
      (e U O B c delta).mapDerivedCategory ≅
    ((e U O B c delta).mapDerivedCategory.op.prod (e U O B c delta).mapDerivedCategory) ⋙
      proEtaleCoefficientHom U.left B
  /-- The required natural internal Hom isomorphism. -/
  homComparison : proEtaleCoefficientHom X O ⋙ (f U O B c).mapDerivedCategory ≅
    ((f U O B c).mapDerivedCategory.op.prod (f U O B c).mapDerivedCategory) ⋙
      proEtaleCoefficientHom U.left B

/-- The ordinary monoidal portion of the comparison, before internal Hom is considered. -/
structure TensorData where
  /-- Delta on module inverse image, with the scalar action transported by b. -/
  ordinary : f U O B c ≅ r U O ⋙ e U O B c delta
  /-- Exact normalized tensor descent for restriction. -/
  restrictionTensor : @ProEtaleSliceTensorDescent X U.left O (proEtaleSliceRing U O)
    (r U O) (r_additive U O) (r_limits U O) (r_colimits U O) S SR T TR
  /-- Exact normalized tensor descent for scalar transport. -/
  scalarTensor : ProEtaleSliceTensorDescent (proEtaleSliceRing U O) B
    (e U O B c delta) SR SB TR TB
  /-- The canonical ordinary restriction unit. -/
  restrictionUnit : (r U O).obj (proEtaleCoefficientUnit X O) ≅
    proEtaleCoefficientUnit U.left (proEtaleSliceRing U O)
  /-- The scalar unit sends a to b(a). -/
  scalarUnit : (e U O B c delta).obj
    (proEtaleCoefficientUnit U.left (proEtaleSliceRing U O)) ≅ proEtaleCoefficientUnit U.left B
  /-- The pullback unit, retaining the prescribed coefficient structure map. -/
  pullbackUnit : (f U O B c).obj (proEtaleCoefficientUnit X O) ≅
    proEtaleCoefficientUnit U.left B

/-- Forget the internal-Hom fields while retaining all ordinary and tensor maps. -/
def Data.tensorData (d : Data U O B c delta S SR SB T TR TB) :
    TensorData U O B c delta S SR SB T TR TB where
  ordinary := d.ordinary
  restrictionTensor := d.restrictionTensor
  scalarTensor := d.scalarTensor
  restrictionUnit := d.restrictionUnit
  scalarUnit := d.scalarUnit
  pullbackUnit := d.pullbackUnit

set_option backward.isDefEq.respectTransparency true in
/-- Section and representative equations for the monoidal portion alone. -/
def TensorNormalized (d : TensorData U O B c delta S SR SB T TR TB)
    (tail : Prop := True) : Prop :=
  -- ordinary_section
  (∀ (N : proEtaleRingModules X O) (V : U.left.ProEt)
    (m : N.val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    (d.ordinary.hom.app N).val.app (op V) (proEtaleSlicePullbackSection U O B c N V m) = m) ∧
  -- restriction_chain
  (∀ (P Q : CochainComplex (proEtaleRingModules X O) ℤ)
    (p q n : ℤ) (h : p + q = n) (V : U.left.ProEt)
    (x : (P.X p).val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)))
    (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    ((d.restrictionTensor.chain P Q).hom.f n).val.app (op V)
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) O
        P Q p q n h (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)) x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left)
        (proEtaleSliceRing U O) ((proEtaleComparisonComplex (r U O)).obj P)
        ((proEtaleComparisonComplex (r U O)).obj Q) p q n h (op V) x y) ∧
  -- scalar_chain
  (∀ (P Q : CochainComplex (proEtaleRingModules U.left
    (proEtaleSliceRing U O)) ℤ) (p q n : ℤ) (h : p + q = n) (V : U.left.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((d.scalarTensor.chain P Q).hom.f n).val.app V
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left)
        (proEtaleSliceRing U O) P Q p q n h V x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology U.left) B
        ((proEtaleComparisonComplex (e U O B c delta)).obj P)
        ((proEtaleComparisonComplex (e U O B c delta)).obj Q) p q n h V x y) ∧
  -- restriction_unit_section
  (∀ (V : U.left.ProEtᵒᵖ)
    (a : (proEtaleSliceRing U O).obj.obj V), d.restrictionUnit.hom.val.app V a = a) ∧
  -- scalar_unit_section
  (∀ (V : U.left.ProEtᵒᵖ)
    (a : (proEtaleSliceRing U O).obj.obj V),
    d.scalarUnit.hom.val.app V a = (b U O B c delta).hom.hom.app V a) ∧
  -- pullback_unit_section
  (∀ (V : U.left.ProEt)
    (a : (proEtaleSliceRing U O).obj.obj (op V)),
    d.pullbackUnit.hom.val.app (op V)
      (proEtaleSlicePullbackSection U O B c (proEtaleCoefficientUnit X O) V a) =
        (b U O B c delta).hom.hom.app (op V) a) ∧
  -- tensor_compatibility
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    (rho U O B c S SB T TB).hom.app (L, M) ≫
        SB.tensor.map (Prod.mkHom
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app L)
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app M)) =
      (proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
          (S.tensor.obj (L, M)) ≫
        (e U O B c delta).mapDerivedCategory.map (d.restrictionTensor.rho.hom.app (L, M)) ≫
        d.scalarTensor.rho.hom.app
          ((r U O).mapDerivedCategory.obj L, (r U O).mapDerivedCategory.obj M)) ∧
  -- unit_compatibility
  ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (proEtaleCoefficientUnit X O)) ≫
      (e U O B c delta).mapDerivedCategory.map
        (proEtaleDerivedCoefficientUnit (r U O) d.restrictionUnit).hom ≫
      (proEtaleDerivedCoefficientUnit (e U O B c delta) d.scalarUnit).hom =
    (proEtaleDerivedCoefficientUnit (f U O B c) d.pullbackUnit).hom) ∧ tail

/-- The section, tensor, unit and closed normalizations of the comparison data. -/
def Normalized (d : Data U O B c delta S SR SB T TR TB) : Prop :=
  -- scalar_equivalence
  ((e U O B c delta).IsEquivalence) ∧
  -- scalar_derived_equivalence
  ((e U O B c delta).mapDerivedCategory.IsEquivalence) ∧
  TensorNormalized U O B c delta S SR SB T TR TB d.tensorData (
  -- restriction_hom_normalization
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.restrictionHom.hom.app (op L, M) = coefficientClosedPullbackMap S SR
      (r U O).mapDerivedCategory d.restrictionTensor.rho L M) ∧
  -- scalar_hom_normalization
  (∀ L M : DerivedCategory
    (proEtaleRingModules U.left (proEtaleSliceRing U O)),
    d.scalarHom.hom.app (op L, M) = coefficientClosedPullbackMap SR SB
      (e U O B c delta).mapDerivedCategory d.scalarTensor.rho L M) ∧
  -- hom_normalization
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.homComparison.hom.app (op L, M) = coefficientClosedPullbackMap S SB
      (f U O B c).mapDerivedCategory (rho U O B c S SB T TB) L M) ∧
  -- hom_transport
  (∀ L M : DerivedCategory (proEtaleRingModules X O),
    d.homComparison.hom.app (op L, M) =
      (proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app
          ((proEtaleCoefficientHom X O).obj (op L, M)) ≫
        (e U O B c delta).mapDerivedCategory.map (d.restrictionHom.hom.app (op L, M)) ≫
        d.scalarHom.hom.app
          (op ((r U O).mapDerivedCategory.obj L), (r U O).mapDerivedCategory.obj M) ≫
        (proEtaleCoefficientHom U.left B).map (Prod.mkHom
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).hom.app L).op
          ((proEtaleSliceDerivedComparison U O B c delta d.ordinary).inv.app M))))

end ProEtaleCoefficientSliceComparison

end AlgebraicGeometry.Scheme
