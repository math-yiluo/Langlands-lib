/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Residue.ResidueFiniteRootMapIso
import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Kummer.KummerComparedBoundaryFormula
import WeilConjectures.AlgebraicGeometry.Kummer.KummerSignedTriangleTransport

/-! # The signed Kummer triangle at one level. -/

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

/-- The finite root map identifies the kernel in the signed multiplication triangle. -/
theorem kummer_compared_kernel_level (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)] (n : ℕ) :
    let M := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf
    let P := (cartierForget (diagonalResidue.{u} ℓ n) W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)
    ∃ (r : Scheme.proEtaleRootsOfUnitySheaf W (ℓ ^ (n + 1)) ≅ P) (i : P ⟶ M),
      r.hom = cartierProRootMap (diagonalResidue.{u} ℓ n)
        (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W
        (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1)) ∧
      Mono i ∧
      Pretriangulated.Triangle.mk
        (ℓ ^ (n + 1) • 𝟙 (((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)⟦(1 : ℤ)⟧))
        (-((kummerComparedUnit ℓ W hW n).hom⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory (DiagonalAb W)) (1 : ℤ) 1).inv.app
            ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj P)))
        (((DerivedCategory.singleFunctor (DiagonalAb W) 0).map (-i))⟦(2 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory (DiagonalAb W)) (1 : ℤ) 1).hom.app
            ((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)) ∈
          distTriang (DerivedCategory (DiagonalAb W)) ∧
      r.hom ≫ i ≫ cartierUnitsComparison W =
        Scheme.proEtaleRootsOfUnityInclusion W (ℓ ^ (n + 1)) := by
  classical
  let M := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf
  let P := (cartierForget (diagonalResidue.{u} ℓ n) W).obj
    (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
  have hunit : IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(W, ⊤)) := by
    simpa only [Nat.cast_pow] using hW.pow (n + 1)
  have hroot : IsIso (cartierProRootMap (diagonalResidue.{u} ℓ n)
      (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W
      (pow_pos (Fact.out : ℓ.Prime).pos _) hunit) := by
    have : IsIso (Etale.ordinaryFiniteRootMap (diagonalResidue.{u} ℓ n)
        (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W) :=
      Etale.residueFiniteRootMap_isIso W _ _
    have : IsIso (cartierForgetComparison (diagonalResidue.{u} ℓ n) W
        (Scheme.finiteEtaleTateLine W (ℓ ^ (n + 1)) (diagonalResidue.{u} ℓ n)
          (cartierResidue_cast ℓ (n + 1)))) := by
      unfold cartierForgetComparison
      erw [← forgetComparisonIso_hom (diagonalResidue.{u} ℓ n) W]
      infer_instance
    let e := (cartierRootsIso W (ℓ ^ (n + 1))
        (pow_pos (Fact.out : ℓ.Prime).pos _) hunit).symm ≪≫
      (comparisonUpperStar AddCommGrpCat.{u + 1} W).mapIso
        (asIso (Etale.ordinaryFiniteRootMap (diagonalResidue.{u} ℓ n)
          (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W)) ≪≫
      asIso (cartierForgetComparison (diagonalResidue.{u} ℓ n) W
        (Scheme.finiteEtaleTateLine W (ℓ ^ (n + 1)) (diagonalResidue.{u} ℓ n)
          (cartierResidue_cast ℓ (n + 1))))
    exact inferInstanceAs (IsIso e.hom)
  let r : Scheme.proEtaleRootsOfUnitySheaf W (ℓ ^ (n + 1)) ≅ P :=
    @asIso _ _ _ _ _ hroot
  let a : M ≅ Scheme.proEtaleUnitsSheaf W :=
    @asIso _ _ _ _ (cartierUnitsComparison W) (unitsComparison_isIso W)
  obtain ⟨i, hi, ht, hin⟩ := proEtale_signed_kummer_triangle W (ℓ ^ (n + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) hunit M P a r
    (kummerComparedUnit ℓ W hW n).hom (kummer_compared_boundary_formula ℓ W hW n)
  refine ⟨r, i, rfl, hi, ?_, ?_⟩
  · exact ht
  · exact hin

end AlgebraicGeometry.ProEtale
