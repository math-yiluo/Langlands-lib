/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect

/-!
# Tensor compatibility for étale sum extension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
thm-asd-smooth-tensor.md, proof paragraph 3 (blueprint: lem-asd-etale-sum-extension-tensor).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u u'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

-- Prefer the direct sheaf-colimit construction when elaborating the derived adjunction.
attribute [local instance 2000] Sheaf.instHasColimitsOfShape

/-- The canonical tensor comparison for exact, termwise derived inverse image. Transport
`leftDerivedUpperStarTensorIso` through `leftDerivedUpperStarIsoMapDerivedCategory` in both
arguments and in the value. Source: Stacks, Tag 0G7E and the tensor comparison in
lem-weil-pbc-ringed-topoi-derived-tensor-pullback
(blueprint: lem-asd-etale-sum-extension-tensor). -/
noncomputable def etaleSumExtensionTensorPullbackIso
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (v : V ⟶ T)
    (B C : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj B)).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≅
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} A) T).obj B).obj C) :=
  ((derivedTensor (ModuleCat.{u + 1} A) V).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app B).symm).app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app C).symm ≪≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v B C).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app _

attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
    leftDerivedUpperStarIsoMapDerivedCategory etaleLowerShriek upperStar

private theorem projection_formula
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {G : C ⥤ D} [G.Monoidal] {L : D ⥤ C} (adj : L ⊣ G)
    (θ : ∀ X Y : C, G.obj X ⊗ G.obj Y ≅ G.obj (X ⊗ Y))
    (hθ : ∀ X Y, Functor.LaxMonoidal.μ G X Y = (θ X Y).hom)
    (B : C) (M : D) [IsIso (Functor.Monoidal.projectionMap adj B)] :
    IsIso ((adj.homEquiv _ _).symm
      (G.obj B ◁ adj.unit.app M ≫ (θ B (L.obj M)).hom)) ∧
    ∀ N : C,
      (adj.homEquiv _ _).symm
          (G.obj B ◁ adj.unit.app (G.obj N) ≫ (θ B (L.obj (G.obj N))).hom) ≫
          B ◁ adj.counit.app N =
        L.map (θ B N).hom ≫ adj.counit.app (B ⊗ N) := by
  have he (P : D) : (adj.homEquiv _ _).symm
      (G.obj B ◁ adj.unit.app P ≫ (θ B (L.obj P)).hom) =
      (Functor.Monoidal.projectionMap adj B).app P := by
    simp only [Adjunction.homEquiv_counit, Functor.Monoidal.projectionMap, hθ]
  constructor
  · rw [he]
    infer_instance
  · intro N
    rw [he, ← hθ]
    simp only [Functor.Monoidal.projectionMap, Category.assoc]
    rw [← adj.counit_naturality, ← Functor.map_comp_assoc]
    congr 1
    rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
      ← MonoidalCategory.whiskerLeft_comp_assoc, adj.right_triangle_components,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl

-- Calculate over an abstract coefficient category before specializing to modules.
end AlgebraicGeometry.Etale
