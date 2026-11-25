/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateTensorComparison
import WeilConjectures.CategoryTheory.CounitComparisonComposition

/-! # Derived comparisons from concrete affine models
Source: Stacks Project, Tags 08DW, 06Y1 and 0D5S.
(blueprint: lem-pc-affine-coordinate-derived-comparison). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The comparison on a single K-flat model, before conjugating the supplied H charts. 
(blueprint: lem-pc-affine-coordinate-derived-comparison)
-/
noncomputable def affineCoordinateObjectDerivedComparison
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) (hM : AffineComparisonKFlat a.A M) :
    DerivedCategory.Qh.obj ((affineCoordinateHomotopy b).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback p).obj (DerivedCategory.Qh.obj ((affineCoordinateHomotopy a).obj M)) := by
  have hi : IsIso ((perfectHomTensorCounit p).app ((affineCoordinateHomotopy a).obj M)) :=
    perfectHomTensorCounit_isIso p ((affineCoordinateComplex a).obj M)
      (affineCoordinateComplex_isKFlat a M hM)
  let := hi
  exact (DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings b.X.toRingedSpace))).mapIso
      ((affineCoordinateHomotopyComparison a b φ p hp).app M).symm ≪≫
    (asIso ((perfectHomTensorCounit p).app ((affineCoordinateHomotopy a).obj M))).symm

/-- The inverse-counit comparison is natural between K-flat models.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-affine-coordinate-derived-comparison).
Proof: apply inverseCounitModelNaturality to the natural termwise comparison
and the fixed counit. The K-flatness theorem makes the two counits invertible. -/
theorem affineCoordinateObjectDerivedComparison_naturality
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (M N : CochainComplex (ModuleCat.{u} a.A) ℤ)
    (hM : AffineComparisonKFlat a.A M) (hN : AffineComparisonKFlat a.A N) (f : M ⟶ N) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
        affineCoordinateHomotopy b ⋙ DerivedCategory.Qh).map f ≫
        (affineCoordinateObjectDerivedComparison a b φ p hp N hN).hom =
      (affineCoordinateObjectDerivedComparison a b φ p hp M hM).hom ≫
        (affineCoordinateHomotopy a ⋙ DerivedCategory.Qh ⋙ derivedPullback p).map f := by
  have hiM : IsIso ((perfectHomTensorCounit p).app ((affineCoordinateHomotopy a).obj M)) :=
    perfectHomTensorCounit_isIso p ((affineCoordinateComplex a).obj M)
      (affineCoordinateComplex_isKFlat a M hM)
  have hiN : IsIso ((perfectHomTensorCounit p).app ((affineCoordinateHomotopy a).obj N)) :=
    perfectHomTensorCounit_isIso p ((affineCoordinateComplex a).obj N)
      (affineCoordinateComplex_isKFlat a N hN)
  exact inverseCounitModelNaturality
    (DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings a.X.toRingedSpace)))
    (DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings b.X.toRingedSpace)))
    (perfectHomTensorHomotopy p) (derivedPullback p) (affineCoordinateHomotopy a)
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ affineCoordinateHomotopy b)
    (affineCoordinateHomotopyComparison a b φ p hp) (perfectHomTensorCounit p) f

/-- Conjugate the concrete comparison by the supplied coordinate models. 
(blueprint: lem-pc-affine-coordinate-derived-comparison)
-/
noncomputable def affineCoordinateChartObjectComparison
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) (hM : AffineComparisonKFlat a.A M) :
    b.H.obj (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) ≅
      (derivedPullback p).obj (a.H.obj M) :=
  (affineCoordinateHomotopyIso b).app
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) ≪≫
    affineCoordinateObjectDerivedComparison a b φ p hp M hM ≪≫
    (derivedPullback p).mapIso ((affineCoordinateHomotopyIso a).app M).symm

/-- The chart comparison retains naturality on K-flat models.
Source: Stacks Project, Tag 08DW.
(blueprint: lem-pc-affine-coordinate-derived-comparison).
Proof: conjugate the preceding naturality equation by the two natural chart isos. -/
theorem affineCoordinateChartObjectComparison_naturality
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A)
    (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (M N : CochainComplex (ModuleCat.{u} a.A) ℤ)
    (hM : AffineComparisonKFlat a.A M) (hN : AffineComparisonKFlat a.A N) (f : M ⟶ N) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ b.H).map f ≫
        (affineCoordinateChartObjectComparison a b φ p hp N hN).hom =
      (affineCoordinateChartObjectComparison a b φ p hp M hM).hom ≫
        (a.H ⋙ derivedPullback p).map f := by
  exact conjugateComparisonNaturality _ _ _ _
    (Functor.isoWhiskerLeft ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ))
      (affineCoordinateHomotopyIso b))
    (Functor.isoWhiskerRight (affineCoordinateHomotopyIso a) (derivedPullback p)) f
    (affineCoordinateObjectDerivedComparison a b φ p hp M hM)
    (affineCoordinateObjectDerivedComparison a b φ p hp N hN)
    (affineCoordinateObjectDerivedComparison_naturality a b φ p hp M N hM hN f)

/-- The natural comparison on the full category of two labelled K-flat models. 
(blueprint: lem-pc-affine-coordinate-derived-comparison)
-/
noncomputable def affineCoordinateDerivedComparison :
    AffineCoordinateComparisonFamily.{u, w} := by
  intro a b φ p hp M N hM hN
  let P := fun j : Bool ↦ cond j M N
  have hP : ∀ j, AffineComparisonKFlat a.A (P j) := by
    intro j
    cases j
    · exact hN
    · exact hM
  exact NatIso.ofComponents
    (fun j ↦ affineCoordinateChartObjectComparison a b φ p hp (P j) (hP j))
    (fun {i j} f ↦ affineCoordinateChartObjectComparison_naturality a b φ p hp
      (P i) (P j) (hP i) (hP j) f.hom)

end AlgebraicGeometry
