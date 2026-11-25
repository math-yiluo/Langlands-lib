/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalPureEvaluationTriangle
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PureKernelTriangleComparison

/-! # The generic Kummer normalization proposition and its triangle criterion. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w uC vC
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard

/-- Roots identifications and the evaluated unit equation for a supplied pure
strict-system comparison. This definition constructs no data. -/
@[irreducible] def KummerPureKernelNormalization
    {A B : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    [Category B] [abB : Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)]
    (F : ∀ n, C n ⥤ B)
    (V : ∀ n, C n ⥤ A)
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop)
    (σ : ∀ n, V n ≅ F n ⋙ U) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    : Prop :=
    ∀ (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
    ∃ (roots : H ⋙ U ≅ rootsTower)
      (t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)),
      (∀ n, rootNorm H roots n (t n)) ∧
      ∀ n, (η n).unit.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map b.hom ≫
        ((diagonalEvaluationForget U n).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        (((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).hom.app
          H)⟦(2 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A 0).map
          (U.map (t n).hom ≫ (σ n).inv.app (P n)))⟦(2 : ℤ)⟧' =
        -((κ n).hom⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
            ((DerivedCategory.singleFunctor A 0).obj ((V n).obj (P n))))

/-- Signed multiplication triangles and an ordinary coefficient lift imply the
prescribed root and evaluated-unit normalization. -/
theorem kummer_normalization_of_triangles
    {A B : Type*} [catA : Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    [catB : Category B] [abB : Abelian B]
    [hDerA : HasDerivedCategory.{w} A] [hDerSys : HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [hSys : HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)]
    (TateF : ∀ n, C n ⥤ B) (V : ∀ n, C n ⥤ A)
    (M : A) (R : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ R) →
      ∀ n, (H.obj (op n) ≅ (TateF n).obj (P n)) → Prop)
    (σ : ∀ n, V n ≅ TateF n ⋙ U) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    (rootMap : ∀ n, R.obj (op n) ⟶ (V n).obj (P n))
    (hkernel : KernelTriangleData ℓ M R (fun n ↦ (V n).obj (P n)) rootMap
      (fun n ↦ -((κ n).hom⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
          ((DerivedCategory.singleFunctor A 0).obj ((V n).obj (P n))))))
    (htriangle : ∀ (H : ℕᵒᵖ ⥤ B)
      (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
      PureEvaluationTriangle ℓ L U ad D η M H b)
    (hlift : FiniteKernelLift U R C TateF V P σ rootMap rootNorm) :
    KummerPureKernelNormalization (abA := abA) (abB := abB) (hA := hA)
      ℓ L U ad D C TateF V M R P κ rootNorm σ η := by
  classical
  unfold FiniteKernelLift at hlift
  unfold KernelTriangleData at hkernel
  obtain ⟨r, i, hr, hi, hK, hrt⟩ := hkernel
  unfold KummerPureKernelNormalization
  intro H b
  let F := DerivedCategory.singleFunctor A 0
  let F₂ := F ⋙ shiftFunctor (DerivedCategory A) (2 : ℤ)
  have htri := htriangle H b
  unfold PureEvaluationTriangle at htri
  obtain ⟨d, hd, hdt⟩ := htri
  obtain ⟨roots, a, he, hau⟩ := pure_kernel_triangle_comparison U H M R
    (fun n ↦ (V n).obj (P n)) r i hi ℓ hrt F₂ ((F.obj M)⟦(1 : ℤ)⟧)
    ((shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).app (F.obj M))
    (fun n ↦ ℓ ^ (n + 1) • 𝟙 ((F.obj M)⟦(1 : ℤ)⟧))
    (fun n ↦ (η n).unit.app ((F.obj M)⟦(1 : ℤ)⟧) ≫
      (diagonalPureEvaluationIso U H b n).hom)
    (fun n ↦ -((κ n).hom⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
        (F.obj ((V n).obj (P n))))) d hd hK hdt
  obtain ⟨t, hnorm, ht⟩ := hlift r hr H roots a he
  refine ⟨roots, t, hnorm, ?_⟩
  intro n
  have h := hau n
  rw [← ht n] at h
  simpa only [diagonalPureEvaluationIso, F₂, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc] using h

/-- Shared coefficient parameters for the Kummer normalization. -/
structure KummerNormalizationCoefficients
    {A B : Type*} [Category A] [Abelian A] [hA : HasExt.{w} A]
    [Category B] (U : B ⥤ A) (C : ℕ → Type uC) where
  [catC : ∀ n, Category.{vC} (C n)]
  TateF : ∀ n, C n ⥤ B
  V : ∀ n, C n ⥤ A
  M : A
  R : ℕᵒᵖ ⥤ A
  P : ∀ n, C n
  κ : ∀ n, Ext M ((V n).obj (P n)) 1
  rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ R) →
    ∀ n, (H.obj (op n) ≅ (TateF n).obj (P n)) → Prop
  σ : ∀ n, V n ≅ TateF n ⋙ U
  rootMap : ∀ n, R.obj (op n) ⟶ (V n).obj (P n)

/-- Normalization for a shared coefficient record. This is the original generic
proposition applied to its fields, with no new condition. -/
def KummerNormalizationCoefficients.Normalized
    {A B : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    [Category B] [abB : Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    {U : B ⥤ A} [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {C : ℕ → Type uC} (s : KummerNormalizationCoefficients U C)
    (ℓ : ℕ) (L : A ⥤ B) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (η : ∀ n, DiagonalEvaluationUnit U ad D n) : Prop :=
  KummerPureKernelNormalization (abA := abA) (abB := abB) (hA := hA)
    (catC := s.catC) ℓ L U ad D C s.TateF s.V s.M s.R s.P s.κ s.rootNorm s.σ η

/-- The signed kernel-triangle property for shared coefficients. -/
def KummerNormalizationCoefficients.Kernel
    {A B : Type*} [Category A] [Abelian A] [HasExt.{w} A] [Category B]
    [HasDerivedCategory.{w} A] {U : B ⥤ A}
    {C : ℕ → Type uC} (s : KummerNormalizationCoefficients U C) (ℓ : ℕ) : Prop :=
  letI := s.catC
  KernelTriangleData ℓ s.M s.R (fun n ↦ (s.V n).obj (s.P n)) s.rootMap
    (fun n ↦ -((s.κ n).hom⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor A 0).obj ((s.V n).obj (s.P n)))))

/-- The pure-evaluation triangle property for shared coefficients. -/
def KummerNormalizationCoefficients.PureTriangles
    {A B : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    {U : B ⥤ A} [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {C : ℕ → Type uC} (s : KummerNormalizationCoefficients U C)
    (ℓ : ℕ) (L : A ⥤ B) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (η : ∀ n, DiagonalEvaluationUnit U ad D n) : Prop :=
  ∀ (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj s.M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
    PureEvaluationTriangle ℓ L U ad D η s.M H b

/-- The ordinary finite-lifting property for shared coefficients. -/
def KummerNormalizationCoefficients.FiniteLift
    {A B : Type*} [Category A] [Abelian A] [HasExt.{w} A] [Category B]
    {U : B ⥤ A} {C : ℕ → Type uC} (s : KummerNormalizationCoefficients U C) : Prop :=
  letI := s.catC
  FiniteKernelLift U s.R C s.TateF s.V s.P s.σ s.rootMap s.rootNorm

/-- The generic triangle criterion with its coefficient parameters shared. -/
theorem kummer_normalization_of_coefficients
    {A B : Type*} [catA : Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    [catB : Category B] [abB : Abelian B]
    [hDerA : HasDerivedCategory.{w} A] [hDerSys : HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [hSys : HasExt.{w} (ℕᵒᵖ ⥤ B)]
    {U : B ⥤ A} [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {C : ℕ → Type uC} (s : KummerNormalizationCoefficients U C)
    (ℓ : ℕ) (L : A ⥤ B) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    (hkernel : s.Kernel ℓ)
    (htriangle : s.PureTriangles ℓ L ad D η)
    (hlift : s.FiniteLift) :
    s.Normalized ℓ L ad D η := by
  exact kummer_normalization_of_triangles (catC := s.catC)
    ℓ L U ad D C s.TateF s.V s.M s.R s.P s.κ s.rootNorm s.σ η s.rootMap
    hkernel htriangle hlift

end AlgebraicGeometry.ProEtale
