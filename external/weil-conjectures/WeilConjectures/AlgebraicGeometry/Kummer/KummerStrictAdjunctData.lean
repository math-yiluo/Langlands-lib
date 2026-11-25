/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSheafExt

/-! # Coefficient data for the strict Kummer comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

/-- Conditional scalar-adjunct computation for a strict target, with coefficient
categories and functors shared parameters. The definition produces no object and
asserts no existence of residue lifts. -/
@[irreducible] def KummerTargetAdjunctCompatibility
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)] [abC : ∀ n, Abelian (C n)]
    [hC : ∀ n, HasExt.{w} (C n)]
    (F : ∀ n, C n ⥤ B) [Fadd : ∀ n, (F n).Additive]
    [Flim : ∀ n, PreservesFiniteLimits (F n)]
    [Fcolim : ∀ n, PreservesFiniteColimits (F n)]
    (V : ∀ n, C n ⥤ A) [Vadd : ∀ n, (V n).Additive]
    [Vlim : ∀ n, PreservesFiniteLimits (V n)]
    [Vcolim : ∀ n, PreservesFiniteColimits (V n)]
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ U ≅ rootsTower)
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)),
    (∀ n, rootNorm H roots n (t n)) ∧
    ∀ (n : ℕ) (S : A)
      (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
        (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S)),
      a.hom = diagonalDerivedSingleCounit ℓ L D S →
      ∀ (Q : C n) (s : (D.ordinary.E.obj S).obj (op n) ≅ (F n).obj Q)
        (g : S ⟶ (V n).obj Q),
        HEq (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S ≫ s.hom)) g →
        ∀ (f : Ext S M 1) (e : Ext Q (P n) 2),
          exactFunctorExtImage (F n) e =
            (Ext.mk₀ s.inv).comp
              (((Ext.homEquiv.symm (a.inv ≫ D.T.map f.hom ≫ b.hom)).mapExactFunctor
                ((evaluation ℕᵒᵖ B).obj (op n))).comp
                (Ext.mk₀ (t n).hom) (add_zero 2)) (zero_add 2) →
          (Ext.mk₀ g).comp (e.mapExactFunctor (V n)) (zero_add 2) = -(f.comp (κ n) rfl)

/-- The positive Kummer unit after the comparison isomorphism on units.
This is the actual Ext composite, named to share its coefficient constructions
rather than checking the concrete sheaf abelian structures at each occurrence. -/
@[irreducible] def kummerComparedUnit (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (n : ℕ) :
    Ext.{u + 1} ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
      ((cartierForget (diagonalResidue.{u} ℓ n) W).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) W)) 1 :=
  (Ext.mk₀ (cartierUnitsComparison W)).comp
    (cartierProKummerUnit (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
      (by simpa using hW.pow (n + 1))) (zero_add 1)

/-- The actual roots comparison equation, named before derived specialization.
This is precisely the canonical underlying-map equation, with no chosen data. -/
def kummerRootNormalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (H : DiagonalSystems ℓ W)
    (roots : H ⋙ diagonalForget ℓ W ≅
      Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (n : ℕ) (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)) : Prop :=
  HEq ((diagonalForget ℓ W).map t.hom)
    (roots.hom.app (op n) ≫ cartierProRootMap (diagonalResidue.{u} ℓ n)
      (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W
      (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1)))

/-- The concrete compatibility formula, with its coefficient expressions shared.
This is a real proposition definition and chooses no data. -/
@[irreducible] def kummerStrictAdjunctCompatibilityStatement (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Prop :=
  KummerTargetAdjunctCompatibility
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W) (hB := kummerModuleHasExt _ W)
    (abC := fun n => diagonalModuleSheafAbelian (diagonalResidue.{u} ℓ n) W)
    (hC := fun n => kummerModuleHasExt (diagonalResidue.{u} ℓ n) W)
    (Fadd := fun n => diagonalFiniteToPadicAdditive ℓ n W)
    (Flim := fun n => diagonalFiniteToPadicLimits ℓ n W)
    (Fcolim := fun n => diagonalFiniteToPadicColimits ℓ n W)
    (Vadd := fun n => cartierForgetAdditive (diagonalResidue.{u} ℓ n) W)
    (Vlim := fun n => cartierForgetLimits (diagonalResidue.{u} ℓ n) W)
    (Vcolim := fun n => cartierForgetColimits (diagonalResidue.{u} ℓ n) W)
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

end AlgebraicGeometry.ProEtale
