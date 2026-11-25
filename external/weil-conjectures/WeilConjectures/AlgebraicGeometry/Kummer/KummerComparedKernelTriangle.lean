/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PureKernelTriangleComparison
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Kummer.KummerComparedKernelLevel
import WeilConjectures.AlgebraicGeometry.Kummer.KummerKernelTransition

/-! # The signed Kummer triangle and its actual root transitions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local instance 11000] kummerAbHasExt kummerModuleHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierProRootMap cartierProKummerUnit cartierUnitsComparison
  cartierRootsIso cartierRootsComparison
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension diagonalScalarAdjunction

private theorem kernel_data_of_levelwise
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (ℓ : ℕ) (M : A) (R : ℕᵒᵖ ⥤ A) (P : ℕ → A)
    (rootMap : ∀ n, R.obj (op n) ⟶ P n)
    (q : ∀ n, ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj (P n))⟦(2 : ℤ)⟧)
    {N : A} (a : M ≅ N) (j : ∀ n, R.obj (op n) ⟶ N)
    (hlevel : ∀ n, ∃ (r : R.obj (op n) ≅ P n) (i : P n ⟶ M),
      r.hom = rootMap n ∧ Mono i ∧
      Pretriangulated.Triangle.mk
        (ℓ ^ (n + 1) • 𝟙 (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧)) (q n)
        (((DerivedCategory.singleFunctor A 0).map (-i))⟦(2 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app
            ((DerivedCategory.singleFunctor A 0).obj M)) ∈ distTriang (DerivedCategory A) ∧
      r.hom ≫ i ≫ a.hom = j n)
    (htransition : ∀ (r : ∀ n, R.obj (op n) ≅ P n) (i : ∀ n, P n ⟶ M),
      (∀ n, (r n).hom ≫ i n ≫ a.hom = j n) →
      ∀ n, R.map (homOfLE (Nat.le_succ n)).op ≫ (r n).hom ≫ i n =
        (r (n + 1)).hom ≫ i (n + 1) ≫ (ℓ • 𝟙 M)) :
    KernelTriangleData ℓ M R P rootMap q := by
  classical
  choose r i hr hi hK hin using hlevel
  unfold KernelTriangleData
  exact ⟨r, i, hr, hi, hK, htransition r i hin⟩

/-- The Kummer kernel is the finite Tate line, with its negative shifted boundary
and its power-ell transition. This is an assertion solely about the Kummer sequence;
no derived reduction, supplied pure comparison, or evaluated unit occurs. -/
theorem kummer_compared_kernel_triangle (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)] :
    let M := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf
    let R := Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime)
    let P := fun n ↦ (cartierForget (diagonalResidue.{u} ℓ n) W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)
    let F := DerivedCategory.singleFunctor (DiagonalAb W) 0
    KernelTriangleData ℓ M R P
      (fun n ↦ cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
        (by simpa using hW.pow (n + 1)))
      (fun n ↦ -((kummerComparedUnit ℓ W hW n).hom⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory (DiagonalAb W)) (1 : ℤ) 1).inv.app (F.obj (P n)))) := by
  let M := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf
  let R := Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime)
  let P := fun n ↦ (cartierForget (diagonalResidue.{u} ℓ n) W).obj
    (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
  let F := DerivedCategory.singleFunctor (DiagonalAb W) 0
  let aUnits : M ≅ Scheme.proEtaleUnitsSheaf W :=
    @asIso _ _ _ _ (cartierUnitsComparison W) (unitsComparison_isIso W)
  refine kernel_data_of_levelwise ℓ M R P
      (fun n ↦ cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
        (by simpa using hW.pow (n + 1)))
      (fun n ↦ -((kummerComparedUnit ℓ W hW n).hom⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory (DiagonalAb W)) (1 : ℤ) 1).inv.app (F.obj (P n)))) aUnits
    (fun n ↦ Scheme.proEtaleRootsOfUnityInclusion W (ℓ ^ (n + 1)))
    (fun n ↦ kummer_compared_kernel_level ℓ W hW n) ?_
  intro r i hin
  exact kummer_kernel_transition ℓ W M P aUnits r i hin

end AlgebraicGeometry.ProEtale
