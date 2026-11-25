/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateDerivedComparison
import WeilConjectures.CategoryTheory.CounitComparisonComposition

/-! # The one-model affine chart cocycle
Source: Stacks Project, Tags 08DW, 06Y1 and 0D5S.
(blueprint: lem-pc-affine-coordinate-comparison-chart-cocycle). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The chart object comparisons obey the composition law on one K-flat model.
This is the universal-property calculation after cancelling the fixed counits:
the underived term is `affineCoordinateTensorComparison_comp`, while the derived
term is `perfectHomTensorCounit_comp`; the chart model isomorphisms cancel by
naturality. Source: Stacks Project, Tags 08DW, 06Y1 and 0D5S.
(blueprint: lem-pc-affine-coordinate-comparison-chart-cocycle). -/
theorem affineCoordinateChartObjectComparison_cocycle
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
    (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
    (hr : q ≫ p = r)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ)
    (hM : AffineComparisonKFlat a.A M) :
    c.H.mapIso
        (eqToIso (congrArg (fun t ↦
            ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc) ≪≫
          (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app M) ≪≫
      affineCoordinateChartObjectComparison b c ψ q hq
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
        (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM) ≪≫
      (derivedPullback q).mapIso
        (affineCoordinateChartObjectComparison a b φ p hp M hM) ≪≫
      (perfectHomComposition q p).app (a.H.obj M) ≪≫
      (eqToIso (congrArg (fun t ↦ derivedPullback t) hr)).app (a.H.obj M) =
      affineCoordinateChartObjectComparison a c χ r hs M hM := by
  subst χ
  subst r
  let E := (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)
  let μ := (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app M
  let A := affineCoordinateHomotopy a
  let B := affineCoordinateHomotopy b
  let C := affineCoordinateHomotopy c
  have hiP : IsIso ((perfectHomTensorCounit p).app (A.obj M)) :=
    perfectHomTensorCounit_isIso p ((affineCoordinateComplex a).obj M)
      (affineCoordinateComplex_isKFlat a M hM)
  have hiQ : IsIso ((perfectHomTensorCounit q).app (B.obj (E.obj M))) :=
    perfectHomTensorCounit_isIso q ((affineCoordinateComplex b).obj (E.obj M))
      (affineCoordinateComplex_isKFlat b (E.obj M)
        (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM))
  have hiR : IsIso ((perfectHomTensorCounit (q ≫ p)).app (A.obj M)) :=
    perfectHomTensorCounit_isIso (q ≫ p) ((affineCoordinateComplex a).obj M)
      (affineCoordinateComplex_isKFlat a M hM)
  have hmodel := affineCoordinateHomotopyComparison_comp a b c φ ψ p q hp hq hs M
  have hcomp := counitComparisonComposition
    (DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings a.X.toRingedSpace)))
    (DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings b.X.toRingedSpace)))
    (DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings c.X.toRingedSpace)))
    (perfectHomTensorHomotopy p) (perfectHomTensorHomotopy q)
    (perfectHomTensorHomotopy (q ≫ p))
    (derivedPullback p) (derivedPullback q) (derivedPullback (q ≫ p))
    (perfectHomTensorHomotopyComp q p) (perfectHomComposition q p)
    (perfectHomTensorCounit p) (perfectHomTensorCounit q) (perfectHomTensorCounit (q ≫ p))
    (A.obj M) (B.obj (E.obj M))
    (C.obj (((ModuleCat.extendScalars (ψ.comp φ)).mapHomologicalComplex (.up ℤ)).obj M))
    (C.obj (((ModuleCat.extendScalars ψ).mapHomologicalComplex (.up ℤ)).obj (E.obj M)))
    ((affineCoordinateHomotopyComparison a b φ p hp).app M)
    ((affineCoordinateHomotopyComparison b c ψ q hq).app (E.obj M))
    ((affineCoordinateHomotopyComparison a c (ψ.comp φ) (q ≫ p) hs).app M)
    (C.mapIso μ) (perfectHomTensorCounit_comp q p (A.obj M)) hmodel
  have hchart := conjugateComparisonComposition
    (derivedPullback p) (derivedPullback q) (derivedPullback (q ≫ p))
    (perfectHomComposition q p)
    ((affineCoordinateHomotopyIso a).app M)
    ((affineCoordinateHomotopyIso b).app (E.obj M))
    ((affineCoordinateHomotopyIso c).app
      (((ModuleCat.extendScalars (ψ.comp φ)).mapHomologicalComplex (.up ℤ)).obj M))
    ((affineCoordinateHomotopyIso c).app
      (((ModuleCat.extendScalars ψ).mapHomologicalComplex (.up ℤ)).obj (E.obj M)))
    (c.H.mapIso μ)
    ((affineCoordinateHomotopy c ⋙ DerivedCategory.Qh).mapIso μ)
    (affineCoordinateObjectDerivedComparison a b φ p hp M hM)
    (affineCoordinateObjectDerivedComparison b c ψ q hq (E.obj M)
      (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM))
    (affineCoordinateObjectDerivedComparison a c (ψ.comp φ) (q ≫ p) hs M hM)
    (by apply Iso.ext; exact (affineCoordinateHomotopyIso c).hom.naturality μ.hom)
    hcomp
  have hrefl : (Iso.refl (derivedPullback (q ≫ p))).app (a.H.obj M) = Iso.refl _ := rfl
  simpa only [affineCoordinateChartObjectComparison, eqToIso_refl, Iso.refl_trans,
    hrefl, Iso.trans_refl] using hchart

end AlgebraicGeometry
