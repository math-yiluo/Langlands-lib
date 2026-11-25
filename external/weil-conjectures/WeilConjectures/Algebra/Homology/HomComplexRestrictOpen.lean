/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpenDifferential
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Hom complexes commute with open restriction

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Cohomology on Sites, Section 0A8X.
(blueprint: lem-sc-hom-complex-restrict-open).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace CategoryTheory

private theorem over_products (X : RingedSpace.{u}) (U : Opens X) :
    Limits.PreservesLimitsOfShape (Discrete ℤ)
      (SheafOfModules.overFunctor.{u} (moduleRings X) U) := by
  let T := SheafOfModules.forget.{u} ((moduleRings X).over U) ⋙
    PresheafOfModules.toPresheaf ((moduleRings X).over U).obj
  have : Limits.PreservesLimitsOfShape (Discrete ℤ)
      (SheafOfModules.overFunctor.{u} (moduleRings X) U ⋙ T) := by
    change Limits.PreservesLimitsOfShape (Discrete ℤ)
      ((SheafOfModules.forget.{u} (moduleRings X) ⋙
        PresheafOfModules.toPresheaf (moduleRings X).obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op)
    infer_instance
  have : Limits.ReflectsLimitsOfShape (Discrete ℤ) T :=
    Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact Limits.preservesLimitsOfShape_of_reflects_of_preserves _ T

private theorem fan_iso {C : Type*} [Category C] {ι : Type*}
    {A B : C} {f g : ι → C} (π : ∀ i, A ⟶ f i) (τ : ∀ i, B ⟶ g i)
    (hπ : Limits.IsLimit (Limits.Fan.mk A π)) (hτ : Limits.IsLimit (Limits.Fan.mk B τ))
    (e : ∀ i, f i ≅ g i) :
    ∃ a : A ≅ B, ∀ i, a.hom ≫ τ i = π i ≫ (e i).hom := by
  let a := Limits.Fan.IsLimit.lift hτ (fun i ↦ π i ≫ (e i).hom)
  let b := Limits.Fan.IsLimit.lift hπ (fun i ↦ τ i ≫ (e i).inv)
  have ha (i) : a ≫ τ i = π i ≫ (e i).hom := Limits.Fan.IsLimit.fac hτ _ i
  have hb (i) : b ≫ π i = τ i ≫ (e i).inv := Limits.Fan.IsLimit.fac hπ _ i
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Limits.Fan.IsLimit.hom_ext hπ
    intro i
    change (a ≫ b) ≫ π i = (𝟙 A) ≫ π i
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply Limits.Fan.IsLimit.hom_ext hτ
    intro i
    change (b ≫ a) ≫ τ i = (𝟙 B) ≫ τ i
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

-- Applying the differential comparison unfolds the chosen product projection types.
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary sheaf Hom complex commutes with restriction to an open.
No boundedness or K-injectivity assumption is needed.

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Cohomology on Sites, Section 0A8X.

Proof: In degree n the Hom complex is the product, over p in Z, of the
internal Homs from L.X p to M.X (p+n). Open restriction preserves products:
products of sheaves of modules are computed sectionwise and restriction is
precomposition with the forgetful functor from the localized site.
For each factor use SheafOfModules.overHomObjIso, which identifies a local
linear map with the same map on the further localized site. The resulting
product isomorphisms commute with pre- and post-composition. Restriction is
additive, so these isomorphisms identify the differential
 d_M f - (-1)^n f d_L with the differential of the restricted Hom complex.
They therefore define a chain isomorphism. This works also for the empty
open, zero complexes and unbounded complexes: no finite-product truncation
or global-section acyclicity assertion is involved.
(blueprint: lem-sc-hom-complex-restrict-open). -/
theorem homComplex_restrict_open (X : RingedSpace.{u}) (U : Opens X)
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) :
    Nonempty (
      homComplex (R := X.sheaf.over U)
        (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)
        (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≅
      ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (homComplex (R := X.sheaf) L M)) := by
  classical
  let F := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let LF := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let MF := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  let H := homComplex (R := X.sheaf) L M
  let K := homComplex (R := X.sheaf.over U) LF MF
  let π := Classical.choose (homComplex_projections_exists (R := X.sheaf))
  let τ := Classical.choose (homComplex_projections_exists (R := X.sheaf.over U))
  have hπ := Classical.choose_spec (homComplex_projections_exists (R := X.sheaf))
  have hτ := Classical.choose_spec (homComplex_projections_exists (R := X.sheaf.over U))
  have : Limits.PreservesLimitsOfShape (Discrete ℤ) F := over_products X U
  have hp (n : ℤ) : Limits.IsLimit (Limits.Fan.mk (F.obj (H.X n))
      (fun p : ℤ ↦ F.map (π L M n p (p + n) rfl))) :=
    Limits.isLimitFanMkObjOfIsLimit F _ _ (Classical.choice (hπ.1 L M n))
  have ht (n : ℤ) : Limits.IsLimit (Limits.Fan.mk (K.X n)
      (fun p : ℤ ↦ τ LF MF n p (p + n) rfl)) := Classical.choice (hτ.1 LF MF n)
  have hi (n : ℤ) := fan_iso _ _ (hp n) (ht n)
    (fun p : ℤ ↦ SheafOfModules.overHomObjIso (L.X p) (M.X (p + n)) U)
  choose e he using hi
  have he' (n p q : ℤ) (hpq : p + n = q) :
      (e n).hom ≫ τ LF MF n p q hpq =
        F.map (π L M n p q hpq) ≫
          (SheafOfModules.overHomObjIso (L.X p) (M.X q) U).hom := by
    subst q
    exact he n p
  have comm := homComplex_restrict_open_differential X U L M e he'
  exact ⟨(HomologicalComplex.Hom.isoOfComponents e comm).symm⟩


end CategoryTheory
