/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import all WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
import all WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension

/-! # Detection of cyclic Cartier classes after integral restriction
(blueprint: lem-diagonal-cyclic-class-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

attribute [local irreducible] cyclicLine cyclicLineMap derivedScalars

/-- Restriction detects degree-two classes with the supported cyclic constant source.

Source: the supported integral-generator Ext bijection in Cartier reduction,
and exact-functor composition coherence.
(blueprint: lem-diagonal-cyclic-class-restriction).

Proof: forgetting the discrete integral action after finite scalar restriction
is the ordinary abelian forgetful functor. Exact-functor composition coherence
therefore carries equal restricted classes to equal abelian classes. Compose
these with the full supported integral generator. Its existing degree-two Ext
bijection is injective, so the original cyclic classes agree. This uses neither
a choice of class nor a global-section test and includes the empty scheme. -/
theorem diagonalCyclicClass_restrict_injective
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) :
    Function.Injective (fun c : GeoCartierClass (diagonalResidue.{u} l n)
        (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) (diagonalImmersion Y) ↦
      c.mapExactFunctor (diagonalFiniteToPadic l n (diagonalSurface Y))) := by
  let F := diagonalFiniteToPadic l n (diagonalSurface Y)
  let G := diagonalForget l (diagonalSurface Y)
  let H := cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)
  let e : H ≅ F ⋙ G := NatIso.ofComponents (fun N ↦
    { hom := ⟨{ app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
                naturality := by intro U V f; ext x; rfl }⟩
      inv := ⟨{ app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
                naturality := by intro U V f; ext x; rfl }⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl })
    (by intro N N' f; ext U x; rfl)
  intro x y h
  have hx := Ext.mapExactFunctor_comp_mk₀_eq_sheaf F G H e x
  have hy := Ext.mapExactFunctor_comp_mk₀_eq_sheaf F G H e y
  have h' := congrArg (fun z ↦ z.mapExactFunctor G) h
  let P := (lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
    (diagonalImmersion Y)).obj (geoCartierConstant (diagonalResidue.{u} l n)
      (ProjectiveLine Y))
  let Q := geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
    (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
  have hh : x.mapExactFunctor H = y.mapExactFunctor H := by
    apply (Ext.postcomp_bijective (e.app Q) 2).injective
    exact hx.trans ((congrArg (fun z ↦
      (Ext.mk₀ (e.hom.app P)).comp z (zero_add 2)) h').trans hy.symm)
  apply (cartierProIntegralGenerator_ext_bijective (diagonalResidue.{u} l n)
    (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
    (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)).injective
  exact congrArg (fun z ↦
    (Ext.mk₀ (cartierProIntegralGenerator (diagonalResidue.{u} l n)
      (diagonalImmersion Y))).comp z (zero_add 2)) hh

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
