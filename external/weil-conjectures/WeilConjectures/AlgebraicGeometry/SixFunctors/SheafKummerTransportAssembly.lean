/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerSheafConclusion
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerSheafClassCondition
import WeilConjectures.AlgebraicGeometry.Kummer.KummerTransportAssembly

/-! # Assembly over a fixed scheme before diagonal specialization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] CategoryTheory.Abelian.Ext normalizedBoundaryTarget
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

/-- Assemble arbitrary supported sources and finite-class predicates on a scheme. -/
theorem sheaf_kummer_transport_assembly (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (S : DiagonalAb W)
    (Q : ∀ n, Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (g : ∀ n, S ⟶ (cartierForget (diagonalResidue.{u} ℓ n) W).obj (Q n))
    (δ : Ext.{u + 1} S ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf) 1)
    {sourceNorm : sheafKummerSourcePredicate ℓ W D S Q}
    {finiteClass : sheafKummerFinitePredicate ℓ W Q}
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S))
    (ha : a.hom = diagonalDerivedSingleCounit ℓ (diagonalScalarExtension ℓ W) D S)
    (hs : ∀ n, ∃ s : (D.ordinary.E.obj S).obj (op n) ≅
      (diagonalFiniteToPadic ℓ n W).obj (Q n), sourceNorm n s)
    (hg : ∀ n s, sourceNorm n s →
      HEq ((diagonalScalarAdjunction ℓ W).unit.app S ≫
        (diagonalForget ℓ W).map ((D.ordinary.π n).app S ≫ s.hom)) (g n))
    (hc : sheafKummerClassCondition ℓ W hW S Q g δ finiteClass) :
    sheafKummerConclusion ℓ W hW D S Q δ sourceNorm finiteClass a := by
  exact kummer_transport_assembly
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
    ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W) (diagonalScalarAdjunction ℓ W) D
    (fun n => Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (fun n => diagonalFiniteToPadic ℓ n W)
    (fun n => cartierForget (diagonalResidue.{u} ℓ n) W)
    S ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf) δ
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime)) Q
    (fun n => geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
    g (fun n => kummerComparedUnit ℓ W hW n) a ha hs hg
    (kummer_strict_target_transport ℓ W hW D) hc

end AlgebraicGeometry.ProEtale
