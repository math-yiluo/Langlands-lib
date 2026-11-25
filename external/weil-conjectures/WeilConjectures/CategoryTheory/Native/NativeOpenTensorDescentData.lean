/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData

/-! # Native open tensor descent components

Source: Stacks 0GL1, 06YN and 012Z; native open tensor proof steps 3--6.
(blueprint: def-sf-native-open-tensor-descent-components)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOfSpec false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero
  AlgebraicGeometry.ProEtaleWeilSheaf.upperStar
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorTotal
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorModel
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorInsertion

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v w

/-- The common inputs to the two independent open tensor descent calculations.
No chain or derived open comparison is included.
Source: Stacks 0GL1 and 07A4; the input fields of OpenTensorPresentation.
(blueprint: def-sf-native-open-tensor-descent-components) -/
structure OpenTensorDescentInput
    (A B : Type v) [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] where
  /-- Actual extension on sheaves. -/
  E : A ⥤ B
  /-- Actual restriction on sheaves. -/
  R : B ⥤ A
  /-- Extension is additive. -/
  [e_add : E.Additive]
  /-- Restriction is additive. -/
  [r_add : R.Additive]
  /-- Extension is exact on the left. -/
  [e_lim : PreservesFiniteLimits E]
  /-- Extension is exact on the right. -/
  [e_colim : PreservesFiniteColimits E]
  /-- Restriction is exact on the left. -/
  [r_lim : PreservesFiniteLimits R]
  /-- Restriction is exact on the right. -/
  [r_colim : PreservesFiniteColimits R]
  /-- The chosen zero preservation for complex extension. -/
  [e_zero : E.PreservesZeroMorphisms]
  /-- The chosen zero preservation for complex restriction. -/
  [r_zero : R.PreservesZeroMorphisms]
  /-- Tensor on open sheaves, left argument first. -/
  SA : A × A ⥤ A
  /-- Tensor on ambient sheaves, left argument first. -/
  SB : B × B ⥤ B
  /-- The recorded direct-sum total tensor on the open. -/
  TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ
  /-- The recorded direct-sum total tensor on the ambient site. -/
  TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ
  /-- Derived tensor on the open. -/
  DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A
  /-- Derived tensor on the ambient site. -/
  DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B
  /-- Categorical two-sided K-flatness on the open. -/
  flatA : CochainComplex A ℤ → Prop
  /-- Categorical two-sided K-flatness on the ambient site. -/
  flatB : CochainComplex B ℤ → Prop

section

attribute [local instance] OpenTensorDescentInput.e_add OpenTensorDescentInput.r_add
  OpenTensorDescentInput.e_lim OpenTensorDescentInput.e_colim
  OpenTensorDescentInput.r_lim OpenTensorDescentInput.r_colim
  OpenTensorDescentInput.e_zero OpenTensorDescentInput.r_zero

/-- Representative models and sheaf maps for a fixed descent input.
Source: the corresponding fields of OpenTensorPresentation, Stacks 0GL1 and 07A4.
(blueprint: def-sf-native-open-tensor-descent-components) -/
structure OpenTensorDescentModels
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (c : OpenTensorDescentInput A B) where
  /-- Chosen native K-flat model on the open. -/
  modelA : ∀ P T, c.flatA P → c.flatA T →
    (c.DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((c.TA.obj P).obj T))
  /-- Chosen native K-flat model on the ambient site. -/
  modelB : ∀ P T, c.flatB P → c.flatB T →
    (c.DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((c.TB.obj P).obj T))
  /-- Actual summand insertions on the open. -/
  iA : ∀ P T (p q n : ℤ), p + q = n →
    (c.SA.obj (P.X p, T.X q) ⟶ ((c.TA.obj P).obj T).X n)
  /-- Actual summand insertions on the ambient site. -/
  iB : ∀ P T (p q n : ℤ), p + q = n →
    (c.SB.obj (P.X p, T.X q) ⟶ ((c.TB.obj P).obj T).X n)
  /-- The normalized balanced sheaf isomorphism. -/
  sheafGamma : ∀ M N, c.SB.obj (c.E.obj M, N) ≅ c.E.obj (c.SA.obj (M, c.R.obj N))
  /-- The canonical balanced sheaf restriction/tensor comparison. -/
  sheafRestriction : ∀ M N, c.R.obj (c.SB.obj (M, N)) ≅ c.SA.obj (c.R.obj M, c.R.obj N)

/-- Extension comparisons for a fixed tensor descent input.
Source: Stacks 0GL1 and 06YN.
(blueprint: def-sf-native-open-tensor-descent-components) -/
structure OpenTensorExtensionDescentData
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c) where
  /-- Extension preserves the fixed K-flat predicate. -/
  hE : ∀ P, c.flatA P → c.flatB ((c.E.mapHomologicalComplex (.up ℤ)).obj P)
  /-- Restriction preserves the fixed K-flat predicate. -/
  hR : ∀ T, c.flatB T → c.flatA ((c.R.mapHomologicalComplex (.up ℤ)).obj T)
  /-- The total projection comparison. -/
  total : ∀ P T, (c.TB.obj ((c.E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
    (c.E.mapHomologicalComplex (.up ℤ)).obj
      ((c.TA.obj P).obj ((c.R.mapHomologicalComplex (.up ℤ)).obj T))
  /-- Its derived comparison. -/
  gamma : c.E.mapDerivedCategory.prod (𝟭 _) ⋙ c.DB ≅
    (𝟭 _).prod c.R.mapDerivedCategory ⋙ c.DA ⋙ c.E.mapDerivedCategory
  /-- The total comparison has the prescribed sheaf summands. -/
  summands : OpenTensorSummandNormalization c.E c.R c.SA c.SB c.TA c.TB
    m.iA m.iB m.sheafGamma total
  /-- The derived comparison has the prescribed representative square. -/
  model : OpenTensorRepresentativeNormalization c.E c.R c.TA c.TB c.DA c.DB
    c.flatA c.flatB hE hR m.modelA m.modelB total gamma

/-- Restriction comparisons for a fixed tensor descent input.
Source: Stacks 07A4 and 06YN.
(blueprint: def-sf-native-open-tensor-descent-components) -/
structure OpenTensorRestrictionDescentData
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c) where
  /-- Restriction preserves the fixed K-flat predicate. -/
  hR : ∀ T, c.flatB T → c.flatA ((c.R.mapHomologicalComplex (.up ℤ)).obj T)
  /-- The total restriction comparison. -/
  total : ∀ P T, (c.R.mapHomologicalComplex (.up ℤ)).obj ((c.TB.obj P).obj T) ≅
    (c.TA.obj ((c.R.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((c.R.mapHomologicalComplex (.up ℤ)).obj T)
  /-- Its derived comparison. -/
  rho : c.DB ⋙ c.R.mapDerivedCategory ≅
    c.R.mapDerivedCategory.prod c.R.mapDerivedCategory ⋙ c.DA
  /-- The total comparison has the prescribed sheaf summands. -/
  summands : ∀ P T (p q n : ℤ) (h : p + q = n),
    c.R.map (m.iB P T p q n h) ≫ (total P T).hom.f n =
      (m.sheafRestriction (P.X p) (T.X q)).hom ≫
        m.iA ((c.R.mapHomologicalComplex (.up ℤ)).obj P)
          ((c.R.mapHomologicalComplex (.up ℤ)).obj T) p q n h
  /-- The derived comparison has the prescribed representative square. -/
  model : OpenTensorRestrictionNormalization c.R c.TA c.TB c.DA c.DB
    c.flatA c.flatB hR m.modelA m.modelB total rho

end

end CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The actual native inputs, supplied without any comparison-existence assertion.

Source: native open operations and Stacks 0GL1/07A4.
Every field is the existing native construction. Models and sheaf maps are kept
in a separate record with explicit compatibility equalities.
(blueprint: def-sf-native-open-tensor-descent-components) -/
def nativeOpenTensorDescentInput :
    OpenTensorDescentInput (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z) :=
  { E := extensionByZero k₀ l j
    R := upperStar k₀ l j
    e_add := inferInstance
    r_add := inferInstance
    e_lim := inferInstance
    e_colim := inferInstance
    r_lim := inferInstance
    r_colim := inferInstance
    e_zero := inferInstance
    r_zero := inferInstance
    SA := nativeOpenSheafTensor k₀ l U
    SB := nativeOpenSheafTensor k₀ l Z
    TA := nativeTensorTotal k₀ l U
    TB := nativeTensorTotal k₀ l Z
    DA := nativeDerivedTensor k₀ l U
    DB := nativeDerivedTensor k₀ l Z
    flatA := NativeIsKFlat k₀ l U
    flatB := NativeIsKFlat k₀ l Z
 }

/-- The representative and sheaf fields agree with the actual native ones.
Source: the compatibility fields of the native open tensor presentation.
(blueprint: def-sf-native-open-tensor-descent-components) -/
structure NativeOpenTensorModelsCompatibility (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)) : Prop where
  /-- The open representative is the native one. -/
  modelA : HEq m.modelA (nativeOpenTensorModel k₀ l U)
  /-- The ambient representative is the native one. -/
  modelB : HEq m.modelB (nativeOpenTensorModel k₀ l Z)
  /-- The open insertion is the native one. -/
  iA : HEq m.iA (nativeOpenTensorInsertion k₀ l U)
  /-- The ambient insertion is the native one. -/
  iB : HEq m.iB (nativeOpenTensorInsertion k₀ l Z)
  /-- The extension comparison is the prescribed sheaf map. -/
  sheafGamma : HEq m.sheafGamma s.sheafGamma
  /-- The restriction comparison is the prescribed sheaf map. -/
  sheafRestriction : HEq m.sheafRestriction s.sheafRestriction

/-- The normalized extension component with its actual representative and sheaf data.
Source: Stacks 0GL1 and 06YN.
(blueprint: def-sf-native-open-tensor-descent-components) -/
structure NativeOpenTensorExtensionDescentData (s : NativeOpenTensorData k₀ l j) where
  /-- The representative models and sheaf maps. -/
  models : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)
  /-- The extension comparison and its normalizations. -/
  component : OpenTensorExtensionDescentData (nativeOpenTensorDescentInput k₀ l j) models
  /-- Every model and sheaf map is the fixed native one. -/
  compatible : NativeOpenTensorModelsCompatibility k₀ l j s models
  /-- The comparison with exactly the native functor types. -/
  gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j
  /-- It is the normalized generic comparison. -/
  gamma_compatible : HEq component.gamma gamma

/-- The normalized restriction component with its actual representative and sheaf data.
Source: Stacks 07A4 and 06YN.
(blueprint: def-sf-native-open-tensor-descent-components) -/
structure NativeOpenTensorRestrictionDescentData (s : NativeOpenTensorData k₀ l j)
    (models : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)) where
  /-- The restriction comparison and its normalizations. -/
  component : OpenTensorRestrictionDescentData (nativeOpenTensorDescentInput k₀ l j) models
  /-- Every model and sheaf map is the fixed native one. -/
  compatible : NativeOpenTensorModelsCompatibility k₀ l j s models
  /-- The comparison with exactly the native functor types. -/
  rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
    (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U
  /-- It is the normalized generic comparison. -/
  rho_compatible : HEq component.rho rho

end AlgebraicGeometry.ProEtaleWeilSheaf
