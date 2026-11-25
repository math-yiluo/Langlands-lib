/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern
import WeilConjectures.AlgebraicGeometry.ScalarData.ScalarModelUnit
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarCounitNormalization
/-! # The scalar counit on an arbitrary root module -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings

/-- The transpose of lineComparison is the ordinary scalar unit on the root module.
Source: classes proof (2), Stacks 06YY and 07A6.
(blueprint: lem-sfb-scalar-root-transpose).
Proof: use the arbitrary-complex model-unit equation on the single root complex.
Naturality of the exact restriction comparison moves the single comparison past
restriction. The ordinary adjunction on single complexes then gives the single of
its unit. This uses no flatness of the root module. -/
theorem scalarRootTranspose (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) :
    (c.scalar.adjunction.homEquiv _ _) (lineComparison l E c) ≫
      ((SemilinearSections.res (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor
        0).hom.app (lineModule l E c) =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
        (c.scalar.ordinaryAdjunction.unit.app c.rootModule) := by
  let s := c.scalar
  let G := SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T)
  let P := (HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0).obj c.rootModule
  let Q := (HomologicalComplex.single (Systems T (Arings l E T)) (.up ℤ) 0).obj
    (s.model.E.obj c.rootModule)
  let e := (HomologicalComplex.singleMapHomologicalComplex s.model.E (.up ℤ) 0).hom.app
    c.rootModule
  have hg : (G.mapDerivedCategorySingleFunctor 0).hom.app (s.model.E.obj c.rootModule) =
      G.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app
          (s.model.E.obj c.rootModule)) := by
    erw [← G.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
    erw [Iso.hom_inv_id_app_assoc]
  have hrep : lineComparison l E c = s.model.ε.app P ≫ DerivedCategory.Q.map e := by
    simp only [lineComparison, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom,
      Iso.refl_inv, NatTrans.id_app]
    erw [s.T.map_id, Category.id_comp, Category.comp_id]
  have ht := s.unit_model P
  rw [hrep, Adjunction.homEquiv_unit]
  change (s.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
    G.mapDerivedCategory.map (s.model.ε.app P ≫ DerivedCategory.Q.map e)) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (s.model.E.obj c.rootModule) = _
  rw [hg]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [G.mapDerivedCategoryFactors.hom.naturality_assoc e]
  erw [reassoc_of% ht]
  simp only [Functor.comp_map]
  repeat' erw [← DerivedCategory.Q.map_comp]
  apply DerivedCategory.Q.congr_map
  have hs := AlgebraicGeometry.ProEtale.SpTowerClasses.singleAdjunct
    s.ordinaryAdjunction (𝟙 (s.model.E.obj c.rootModule))
  simp only [Adjunction.homEquiv_unit] at hs
  repeat' first
    | erw [CategoryTheory.Functor.map_id] at hs
    | erw [Category.comp_id] at hs
  simpa only [Category.assoc, CochainComplex.singleFunctors] using hs
end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
