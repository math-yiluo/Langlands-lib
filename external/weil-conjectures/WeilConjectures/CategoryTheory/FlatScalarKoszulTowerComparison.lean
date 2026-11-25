/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.CategoryTheory.FlatScalarKoszulModels
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-! # Flat scalar restriction of the strict Koszul tower

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags 0A07
and 0941; more-algebra.tex, Tag 0913.
(auxiliary; not a blueprint node).

## Main statements

* `flatScalarKoszulTowerComparison`: strict and derived normalized comparisons.

The coordinate maps below use the ordered tensor basis of the positive Koszul complex,
its dual evaluation, and the coproduct maps of total tensor. They specify actual maps,
so the comparison cannot be changed by a simultaneous choice of coordinates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}

variable {R B : Sheaf J CommRingCat.{u}}
variable [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules B)]
variable [HasDerivedCategory.{w} (Towers R)] [HasDerivedCategory.{w} (Towers B)]

/-- Exact scalar restriction on unbounded derived categories. Source: Stacks 0A07
(auxiliary; not a blueprint node). -/
abbrev restrictDerived (φ : R ⟶ B) := (restriction φ).mapDerivedCategory

/-- The canonical ordinary inverse-limit projection, applied degreewise.
Source: Stacks 0941
(auxiliary; not a blueprint node). -/
abbrev limitProjection (O : Sheaf J CommRingCat.{u}) (m : ℕᵒᵖ) :=
  NatTrans.mapHomologicalComplex
    (lim.π m : (lim : Towers O ⥤ Modules O) ⟶ (evaluation ℕᵒᵖ (Modules O)).obj m) (.up ℤ)

private theorem tensorUnit_naturality (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) (m : ℕᵒᵖ) :
    f ≫ ringedKoszulTensorUnitComponent O r b M m =
      ringedKoszulTensorUnitComponent O r b N m ≫
        ((ringedKoszulTensorTower O r b).map f).app m := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  have hn := ((ringedKoszulTensor O).map f).naturality (ringedKoszulDualUnit O r b m.unop)
  dsimp only [ringedKoszulTensorUnitComponent, ringedKoszulTensorTower,
    Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  rw [← Category.assoc]
  have hu : f ≫ (ringedKoszulRightUnitIso O M).inv =
      (ringedKoszulRightUnitIso O N).inv ≫
        ((ringedKoszulTensor O).map f).app (ringedSiteRingComplex O) := by
    exact rightUnitor_inv_naturality f
  rw [hu, Category.assoc, ← hn, ← Category.assoc]

attribute [local irreducible] ringedKoszulTensor ringedKoszulDualTower
  ringedKoszulDiagram SheafOfModules.monoidalCategory coordinate dualCoordinate
  positiveBasis factorBasis degree

private def ordinaryUnitNat (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    𝟭 (ringedSiteComplex O) ⟶ ringedKoszulTensorTowerFunctor O r b ⋙ limitComplex O where
  app N := ringedKoszulLimitUnit O r b N
  naturality {N M} f := by
    apply HomologicalComplex.hom_ext
    intro n
    change f.f n ≫ limit.lift _ (ringedKoszulTensorUnitCone O r b M n) =
      limit.lift _ (ringedKoszulTensorUnitCone O r b N n) ≫
        limMap ((ringedKoszulTensorTowerFunctor O r b).map f |>.f n)
    apply limit.hom_ext
    intro m
    simp only [Category.assoc]
    erw [limit.lift_π, limMap_π]
    rw [← Category.assoc]
    erw [limit.lift_π]
    exact congrArg (fun g ↦ g.f n) (tensorUnit_naturality O r b f m)

private def derivedUnitNat (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) : 𝟭 (ringedSiteDerived O) ⟶ D.completion :=
  let t : DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ D.completion :=
    (DerivedCategory.Q.leftUnitor).inv ≫
    Functor.whiskerRight (ordinaryUnitNat O r b) DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ringedKoszulTensorTowerFunctor O r b) D.comparison ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight D.tensorFactors.inv D.inverseLimit ≫
    (Functor.associator _ _ _).hom
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules O) (.up ℤ)) DerivedCategory.Q
    (DerivedCategory.Q ⋙ D.completion) (𝟭 _) D.completion t

private theorem derivedUnitNat_app_Q (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) (N : ringedSiteComplex O) :
    (derivedUnitNat O D).app (DerivedCategory.Q.obj N) = D.unitOnComplex N := by
  simp only [derivedUnitNat, Localization.liftNatTrans_app]
  dsimp [RingedKoszulLimitPresentation.unitOnComplex, ordinaryUnitNat]
  simp only [Category.id_comp, Category.comp_id]
  rfl

private theorem derivedUnitNat_app (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) (E : ringedSiteDerived O) :
    (derivedUnitNat O D).app E = D.unit E := by
  have hn := (derivedUnitNat O D).naturality (DerivedCategory.Q.objObjPreimageIso E).hom
  dsimp only [Functor.id_map] at hn
  rw [derivedUnitNat_app_Q] at hn
  simp only [RingedKoszulLimitPresentation.unit, ← hn, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

private theorem unit_app_Q (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) (N : ringedSiteComplex O) :
    D.unit (DerivedCategory.Q.obj N) = D.unitOnComplex N := by
  rw [← derivedUnitNat_app, derivedUnitNat_app_Q]

private theorem unit_naturality (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b)
    {E E' : ringedSiteDerived O} (f : E ⟶ E') :
    f ≫ D.unit E' = D.unit E ≫ D.completion.map f := by
  simpa only [Functor.id_map, derivedUnitNat_app] using (derivedUnitNat O D).naturality f

end CategoryTheory.FlatScalarKoszul
