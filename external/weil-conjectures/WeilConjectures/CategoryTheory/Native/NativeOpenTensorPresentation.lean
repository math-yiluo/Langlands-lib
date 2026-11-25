/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # Generic native open tensor presentation records

The existing normalization definitions and presentation records are extracted
verbatim from NativeOpenDerivedTensor to bound compilation time per file.
Source: Stacks 0GL1, 0E8I and the original declaration docstrings
(blueprint: lem-sf-native-open-derived-tensor).
-/

/-! Factored construction (blueprint: def-sf-generic-open-tensor-presentation). -/

@[expose] public noncomputable section

set_option autoImplicit false

universe a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The unit-transpose normalization of an open tensor comparison.
Source: Stacks 0E8I, 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorUnitNormalization {A B : Type a} [Category.{b} A] [Category.{b} B]
    (E : A ⥤ B) (R : B ⥤ A) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (adj : E ⊣ R)
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E) : Prop :=
  ∀ (M : A) (N : B), adj.homEquiv _ _ (gamma.inv.app (M, N)) =
    TA.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ rho.inv.app (E.obj M, N)

/-- The two-sided localization square for a total-complex open tensor map.
The comparison is fixed on arbitrary K-flat representatives.
Source: Stacks 0GL1, 06YN (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorRepresentativeNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hE : ∀ P, flatA P → flatB ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (total : ∀ P T, (TB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
      (E.mapHomologicalComplex (.up ℤ)).obj
        ((TA.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T)))
    (gamma : E.mapDerivedCategory.prod (𝟭 _) ⋙ DB ≅
      (𝟭 _).prod R.mapDerivedCategory ⋙ DA ⋙ E.mapDerivedCategory) : Prop :=
  ∀ P T (hP : flatA P) (hT : flatB T),
    gamma.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      E.mapDerivedCategory.map
        (DA.map (Prod.mkHom (𝟙 _) (R.mapDerivedCategoryFactors.hom.app T))) ≫
      E.mapDerivedCategory.map
        (modelA P ((R.mapHomologicalComplex (.up ℤ)).obj T) hP (hR T hT)).hom ≫
      E.mapDerivedCategoryFactors.hom.app _ =
    DB.map (Prod.mkHom (E.mapDerivedCategoryFactors.hom.app P) (𝟙 _)) ≫
      (modelB ((E.mapHomologicalComplex (.up ℤ)).obj P) T (hE P hP) hT).hom ≫
        DerivedCategory.Q.map (total P T).hom

/-- Localization normalization of restriction/tensor, on arbitrary K-flat inputs.
Source: Stacks 0GL1, 06YN (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorRestrictionNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (R : B ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (total : ∀ P T, (R.mapHomologicalComplex (.up ℤ)).obj ((TB.obj P).obj T) ≅
      (TA.obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (rho : DB ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA) : Prop :=
  ∀ P T (hP : flatB P) (hT : flatB T),
    rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      DA.map (Prod.mkHom (R.mapDerivedCategoryFactors.hom.app P)
        (R.mapDerivedCategoryFactors.hom.app T)) ≫
      (modelA _ _ (hR P hP) (hR T hT)).hom =
    R.mapDerivedCategory.map (modelB P T hP hT).hom ≫
      R.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map (total P T).hom

/-- Forgetting the equivariant open map gives the ordinary map under the specified
open and tensor comparisons. Both inverses are fixed by the same square.
Source: Stacks 0GL1; native closed-forgetful normalization
(blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorForgetNormalization
    {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
    [Category.{b} A'] [Category.{b} B']
    (E : A ⥤ B) (R : B ⥤ A) (E' : A' ⥤ B') (R' : B' ⥤ A')
    (FA : A ⥤ A') (FB : B ⥤ B')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (tA : TA ⋙ FA ≅ FA.prod FA ⋙ TA')
    (tB : TB ⋙ FB ≅ FB.prod FB ⋙ TB')
    (gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E)
    (gamma' : E'.prod (𝟭 B') ⋙ TB' ≅ (𝟭 A').prod R' ⋙ TA' ⋙ E') : Prop :=
  ∀ M N, FB.map (gamma.hom.app (M, N)) ≫
      eE.hom.app (TA.obj (M, R.obj N)) ≫ E'.map (tA.hom.app (M, R.obj N)) ≫
      E'.map (TA'.map (Prod.mkHom (𝟙 _) (eR.hom.app N))) =
    tB.hom.app (E.obj M, N) ≫ TB'.map (Prod.mkHom (eE.hom.app M) (𝟙 _)) ≫
      gamma'.hom.app (FA.obj M, FB.obj N)

/-- Every summand of the total open map is its sheaf map. The input insertion maps
are the actual total-complex coproduct insertions, not chosen generators.
Source: Stacks 012Z, 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
def OpenTensorSummandNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    (SA : A × A ⥤ A) (SB : B × B ⥤ B)
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ P T (p q n : ℤ), p + q = n →
      (SA.obj (P.X p, T.X q) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ P T (p q n : ℤ), p + q = n →
      (SB.obj (P.X p, T.X q) ⟶ ((TB.obj P).obj T).X n))
    (sheaf : ∀ M N, SB.obj (E.obj M, N) ≅ E.obj (SA.obj (M, R.obj N)))
    (total : ∀ P T, (TB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
      (E.mapHomologicalComplex (.up ℤ)).obj
        ((TA.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T))) : Prop :=
  ∀ P T (p q n : ℤ) (h : p + q = n),
    iB ((E.mapHomologicalComplex (.up ℤ)).obj P) T p q n h ≫ (total P T).hom.f n =
      (sheaf (P.X p) (T.X q)).hom ≫
        E.map (iA P ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h)

/-- A presentation of the open tensor calculation, with all functors, K-flat models,
and normalizations retained. The theorem pins every functor and representative map
to the existing native constructions, using equality rather than recomputation.
Source: Stacks 0E8I, 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
structure OpenTensorPresentation
    (A B : Type a) [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B] where
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
  /-- Preservation by extension. -/
  hE : ∀ P, flatA P → flatB ((E.mapHomologicalComplex (.up ℤ)).obj P)
  /-- Preservation by restriction. -/
  hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T)
  /-- Chosen native K-flat model on the open. -/
  modelA : ∀ P T, flatA P → flatA T →
    (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TA.obj P).obj T))
  /-- Chosen native K-flat model on the ambient site. -/
  modelB : ∀ P T, flatB P → flatB T →
    (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TB.obj P).obj T))
  /-- Actual summand insertions on the open. -/
  iA : ∀ P T (p q n : ℤ), p + q = n →
    (SA.obj (P.X p, T.X q) ⟶ ((TA.obj P).obj T).X n)
  /-- Actual summand insertions on the ambient site. -/
  iB : ∀ P T (p q n : ℤ), p + q = n →
    (SB.obj (P.X p, T.X q) ⟶ ((TB.obj P).obj T).X n)
  /-- The normalized balanced sheaf isomorphism. -/
  sheafGamma : ∀ M N, SB.obj (E.obj M, N) ≅ E.obj (SA.obj (M, R.obj N))
  /-- Its totalization. -/
  totalGamma : ∀ P T, (TB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj T ≅
    (E.mapHomologicalComplex (.up ℤ)).obj
      ((TA.obj P).obj ((R.mapHomologicalComplex (.up ℤ)).obj T))
  /-- It is termwise the fixed sheaf map. -/
  summands : OpenTensorSummandNormalization E R SA SB TA TB iA iB sheafGamma totalGamma
  /-- The canonical balanced sheaf restriction/tensor comparison. -/
  sheafRestriction : ∀ M N, R.obj (SB.obj (M, N)) ≅ SA.obj (R.obj M, R.obj N)
  /-- The totalization of the same restriction comparison. -/
  totalRestriction : ∀ P T,
    (R.mapHomologicalComplex (.up ℤ)).obj ((TB.obj P).obj T) ≅
      (TA.obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj T)
  /-- Each summand is precisely the balanced sheaf restriction map. -/
  restriction_summands : ∀ P T (p q n : ℤ) (h : p + q = n),
    R.map (iB P T p q n h) ≫ (totalRestriction P T).hom.f n =
      (sheafRestriction (P.X p) (T.X q)).hom ≫
        iA ((R.mapHomologicalComplex (.up ℤ)).obj P)
          ((R.mapHomologicalComplex (.up ℤ)).obj T) p q n h
  /-- The derived restriction comparison. -/
  restriction : DB ⋙ R.mapDerivedCategory ≅
    R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA
  /-- It is the localization of the specified total restriction comparison. -/
  restriction_model : OpenTensorRestrictionNormalization R TA TB DA DB flatA flatB hR
    modelA modelB totalRestriction restriction
  /-- The natural ambient derived isomorphism. -/
  gamma : E.mapDerivedCategory.prod (𝟭 _) ⋙ DB ≅
    (𝟭 _).prod R.mapDerivedCategory ⋙ DA ⋙ E.mapDerivedCategory
  /-- It is the localization of the specified total comparison. -/
  model : OpenTensorRepresentativeNormalization E R TA TB DA DB flatA flatB hE hR
    modelA modelB totalGamma gamma

/-- Normalized comparison with ordinary module categories. Its tensor comparisons
are required to be the canonical ones, and its open maps are fixed by their units.
Source: Stacks 0GL1 and openTensorNormalization
(blueprint: lem-sf-native-open-derived-tensor). -/
structure OpenTensorForgetData
    {A B A' B' : Type a} [Category.{b} A] [Category.{b} B]
    [Category.{b} A'] [Category.{b} B']
    (E : A ⥤ B) (R : B ⥤ A) (E' : A' ⥤ B') (R' : B' ⥤ A')
    (FA : A ⥤ A') (FB : B ⥤ B')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (eE : E ⋙ FB ≅ FA ⋙ E') (eR : R ⋙ FA ≅ FB ⋙ R')
    (tA : TA ⋙ FA ≅ FA.prod FA ⋙ TA')
    (tB : TB ⋙ FB ≅ FB.prod FB ⋙ TB')
    (adj' : E' ⊣ R')
    (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (gamma : E.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod R ⋙ TA ⋙ E) where
  /-- Ordinary restriction with its canonical tensor comparison. -/
  restriction : TB' ⋙ R' ≅ R'.prod R' ⋙ TA'
  /-- On forgotten inputs, restriction/tensor is the canonical native comparison
  under the fixed tensor and open comparisons. Thus it cannot be rescaled. -/
  restriction_compatibility : ∀ M N,
    FA.map (rho.hom.app (M, N)) ≫ tA.hom.app (R.obj M, R.obj N) ≫
      TA'.map (Prod.mkHom (eR.hom.app M) (eR.hom.app N)) =
    eR.hom.app (TB.obj (M, N)) ≫ R'.map (tB.hom.app (M, N)) ≫
      restriction.hom.app (FB.obj M, FB.obj N)
  /-- The ordinary unit-normalized open tensor isomorphism. -/
  gamma' : E'.prod (𝟭 B') ⋙ TB' ≅ (𝟭 A').prod R' ⋙ TA' ⋙ E'
  /-- Exactly the ordinary unit transpose, including the inverse. -/
  inverse_unit : OpenTensorUnitNormalization E' R' TA' TB' adj' restriction gamma'
  /-- Equality after forgetting under the actual open and tensor comparisons. -/
  compatibility : OpenTensorForgetNormalization E R E' R' FA FB TA TB TA' TB'
    eE eR tA tB gamma gamma'

end CategoryTheory
