/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
import WeilConjectures.AlgebraicGeometry.Strict.StrictKummerCohomologyConcentration
import WeilConjectures.AlgebraicGeometry.Strict.StrictKummerPureKernelNormalization

/-! # Strict Kummer target and normalization of its evaluated units
Source: diagonal tower system proof, step (3), target paragraph, and step (4).
(blueprint: lem-sfb-strict-kummer-unit-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierProKummerUnit cartierProRootMap diagonalFiniteToPadic diagonalForget
  diagonalScalarExtension diagonalScalarAdjunction

/-- Normalized target data, with its coefficient classes kept as parameters.
This is the existential roots comparison and its unit equation, packaged to avoid
unfolding coefficient constructions while checking a concrete specialization.
Source: diagonal tower proof, steps (3) and (4)
(blueprint: lem-sfb-strict-kummer-unit-normalization). -/
@[irreducible] def KummerUnitNormalizedTarget
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
    (σ : ∀ n, V n ≅ F n ⋙ U) (η : ∀ n, DiagonalEvaluationUnit U ad D n) : Prop :=
    ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ U ≅ rootsTower)
      (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧)
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

/-- The t-structure constructs the strict comparison from vanishing; kernel
normalization then supplies its roots and finite-level identifications. -/
private theorem kummer_target_of_concentration
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
    (hc : (D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧)).IsGE (-2) ∧
      (D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧)).IsLE (-2))
    (hn : KummerPureKernelNormalization ℓ L U ad D C F V M rootsTower P κ
      rootNorm σ η) :
    KummerUnitNormalizedTarget ℓ L U ad D C F V M rootsTower P κ rootNorm σ η := by
  let := hc.1
  let := hc.2
  obtain ⟨H, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧)) (-2)
  let b := e ≪≫ (((DerivedCategory.singleFunctors (ℕᵒᵖ ⥤ B)).shiftIso
    (2 : ℤ) (-2) 0 (by decide)).app H).symm
  unfold KummerPureKernelNormalization at hn
  have h := hn H b
  obtain ⟨roots, t, ht, he⟩ := h
  unfold KummerUnitNormalizedTarget
  exact ⟨H, roots, b, t, ht, he⟩

/-- The strict Kummer comparison is normalized on the unit of shifted units.
There is no arbitrary source, extension class, or residue lift in this statement.

Source: diagonal tower system proof, step (3), target paragraph, and the
Kummer-unit computation in step (4)
(blueprint: lem-sfb-strict-kummer-unit-normalization).

Proof: compute simultaneous reduction of comparison units on a common K-flat
resolution, comparing evaluation with the two-term resolution of each positive
prime-power coefficient. Kummer exactness and exact site comparison identify
its sole cohomology with roots in degree -1. The transition of resolutions is
multiplication by ell in degree -1 and identity in degree 0, hence induces the
actual power-ell transition on roots. Good truncation in the strict p-adic
system category gives H and its underlying roots isomorphism; its quotient
scalar action and the roots-to-line comparison give t and the displayed
underlying-map equation. Shift the comparison once and choose its negative
normalization to give b. For the unit equation, use the complexes field of the
given evaluated unit on the common K-flat resolution. The positive kernel
inclusion identifies the unshifted coefficient quotient unit with the positive
Kummer connecting morphism. Shifting once introduces the inverse
shiftFunctorAdd comparison; negating b gives the negative of the shifted
positive class. The exact units comparison precedes that class. This is an
equation only on the unit at shifted comparison units; arbitrary-arrow
compatibility follows separately by naturality. All comparisons take place
before forgetting strict transitions. Empty schemes, ell=2, and n=0 use the
same constructions (n+1 is always positive). -/
theorem strict_kummer_unit_normalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) :
  KummerUnitNormalizedTarget
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W)
    ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D
    (fun n => Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (fun n => diagonalFiniteToPadic ℓ n W)
    (fun n => cartierForget (diagonalResidue.{u} ℓ n) W)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (fun n => geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
    (fun n => kummerComparedUnit ℓ W hW n)
    (kummerRootNormalization ℓ W hW)
    (fun n ↦ diagonalFiniteForgetIso ℓ n W) η := by
  apply kummer_target_of_concentration
  · exact strict_kummer_cohomology_concentration ℓ W hW D
  · exact strict_kummer_pure_kernel_normalization ℓ W hW D η

end AlgebraicGeometry.ProEtale
