/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoefficientModel
public import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The underlying additive comparison for finite coefficients

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-coefficient-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})

/-- The actual associated-module-sheaf unit after forgetting coefficients.
Source: Stacks 00YV (blueprint: def-sfb-finite-coefficient-scalar-comparison). -/
def finiteRealizationForgetUnit :
    finiteOrdinaryForget (FiniteRing l E n) T ⟶
      finiteOrdinaryRealization l E n T ⋙ finiteForget l E T n where
  app M :=
    { hom := (PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
          (finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n))).unit.app
          ((finiteCoefficientModulePresheaf T.ProEt (FiniteRing l E n)).obj M.obj)) }
  naturality M N f := by
    apply Sheaf.hom_ext
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
        (finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n))).unit.naturality
        ((finiteCoefficientModulePresheaf T.ProEt (FiniteRing l E n)).map f.hom))

/-- The comparison is invertible because the underlying additive sheaf is already a sheaf.
Source: Stacks 00YV (blueprint: def-sfb-finite-coefficient-scalar-comparison). -/
instance finiteRealizationForgetUnit_isIso :
    IsIso (finiteRealizationForgetUnit l E n T) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← isIso_iff_of_reflects_iso _
    (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})]
  change IsIso ((PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n))).unit.app
        ((finiteCoefficientModulePresheaf T.ProEt (FiniteRing l E n)).obj M.obj)))
  simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  apply isIso_toSheafify
  exact     ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (FiniteRing l E n)) AddCommGrpCat.{u + 1})).obj M).property

/-- Exact site comparison commutes with forgetting the finite coefficient action,
using the actual associated-sheaf unit.
Source: Stacks 00YV, 03FD (blueprint: def-sfb-finite-coefficient-scalar-comparison). -/
def finiteScalarComparison :
    Etale.moduleAbelianForget (FiniteRing l E n) T ⋙
        comparisonUpperStar AddCommGrpCat.{u + 1} T ≅
      finiteOrdinaryComparison (FiniteRing l E n) T ⋙
        finiteOrdinaryRealization l E n T ⋙ finiteForget l E T n :=
  forgetComparisonIso (FiniteRing l E n) T ≪≫
    Functor.isoWhiskerLeft _ (asIso (finiteRealizationForgetUnit l E n T))

/-- The same scalar comparison with the composite functors grouped on the left.
Source: the canonical functor associator
(blueprint: def-sfb-finite-coefficient-scalar-comparison). -/
def finiteScalarCompositeComparison :
    Etale.moduleAbelianForget (FiniteRing l E n) T ⋙
        comparisonUpperStar AddCommGrpCat.{u + 1} T ≅
      (finiteOrdinaryComparison (FiniteRing l E n) T ⋙
        finiteOrdinaryRealization l E n T) ⋙ finiteForget l E T n :=
  finiteScalarComparison l E n T ≪≫
    (Functor.associator (finiteOrdinaryComparison (FiniteRing l E n) T)
      (finiteOrdinaryRealization l E n T) (finiteForget l E T n)).symm

/-- The target coordinate on the underlying additive sheaf of the etale Tate line.
Source: scalar comparison and the specified line coordinate
(blueprint: def-sfb-finite-coefficient-scalar-comparison). -/
def finiteScalarLineCoordinate
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj
          (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
            (ULift.ext (coefficient_annihilates l E n)))) ⟶
      (finiteForget l E T n).obj (finiteLine l E T n) :=
  (finiteScalarComparison l E n T).hom.app _ ≫
    (finiteForget l E T n).map (finiteOrdinaryLineCoordinate l E n T c).hom

/-- The scalar line coordinate has the given comparison component and line map.
Source: its explicit construction
(blueprint: def-sfb-finite-coefficient-scalar-comparison). -/
theorem finiteScalarLineCoordinate_eq
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    finiteScalarLineCoordinate l E n T c =
      ((finiteScalarComparison l E n T).app _).hom ≫
        (finiteForget l E T n).map (finiteOrdinaryLineCoordinate l E n T c).hom := rfl

/-- The additive comparison carries the comparison-adjunction generator to the
actual scalar-unit section. Source: the adjunction mate defining forgetComparisonIso
(blueprint: def-sfb-finite-coefficient-scalar-comparison). -/
theorem finiteScalarComparison_unit_section
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (FiniteRing l E n)))
    (U : T.Etaleᵒᵖ)
    (x : ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj M).obj.obj U) :
    ((finiteScalarComparison l E n T).hom.app M).hom.app ((Scheme.toProEt T).op.obj U)
        (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
          ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj M)).hom.app U x) =
      Scheme.sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _
        ((Scheme.toProEt T).op.obj U)
        (((comparisonAdjunction (ModuleCat.{u + 1} (FiniteRing l E n)) T).unit.app
          M).hom.app U x) := by
  let H := (comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv
    ((Etale.RawModuleScalarComparison.forget (FiniteRing l E n) T).obj M)
    ((finiteOrdinaryComparison (FiniteRing l E n) T ⋙
      sheafCompose (Scheme.ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (FiniteRing l E n)) AddCommGrpCat.{u + 1})).obj M)
  have h := (congrArg H (forgetComparisonIso_hom (FiniteRing l E n) T M)).trans
    (H.apply_symm_apply _)
  have hx := congrArg (fun f ↦ f.hom.app U x) h
  change Scheme.sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _
      ((Scheme.toProEt T).op.obj U)
      (((forgetComparisonIso (FiniteRing l E n) T).hom.app M).hom.app
        ((Scheme.toProEt T).op.obj U)
        (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
          ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj M)).hom.app U x)) = _
  exact congrArg (Scheme.sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _
    ((Scheme.toProEt T).op.obj U)) hx

end AlgebraicGeometry.ProEtale.DiagonalTrace
