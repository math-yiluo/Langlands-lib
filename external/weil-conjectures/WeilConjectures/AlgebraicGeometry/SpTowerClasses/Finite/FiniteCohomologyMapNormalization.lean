/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Exact comparison of a cohomology map with normalized endpoints

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-cohomology-map-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
open FiniteExactArrow
attribute [local instance 100001] finiteIntegralTowerDerived finiteIntegralTowerExt
  finiteIntegralAbDerived finiteIntegralAbExt
  finiteIntegralEtaleDerived finiteIntegralEtaleExt

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison
  HasDerivedCategory.ofIsGrothendieckAbelian HomologicalComplex.quasiIso

/-- Exact comparison of a cohomology map respects a given target factorization,
with any fixed derived source normalization. Source: Sheaf.H.map and naturality
of exact single-arrow transport
(blueprint: lem-sfb-finite-cohomology-map-normalization).

Proof: the Hom of Sheaf.H.map is shifted postcomposition. Exact single-arrow
transport commutes with that postcomposition. Combine the two target single
maps, apply the supplied equality of sheaf maps, then separate their single
and shift images and associate. The statement has no coefficient ring. -/
theorem finiteCohomologyMap_normalization (T : Scheme.{u})
    {M N : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {P Q : DiagonalAb T} (t : M ⟶ N)
    (r : (comparisonUpperStar AddCommGrpCat.{u + 1} T).obj N ⟶ Q)
    (u : (comparisonUpperStar AddCommGrpCat.{u + 1} T).obj M ⟶ P) (v : P ⟶ Q)
    (h : (comparisonUpperStar AddCommGrpCat.{u + 1} T).map t ≫ r = u ≫ v)
    (x : Sheaf.H M 2) {Z : DerivedCategory (DiagonalAb T)}
    (i : Z ⟶ (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) :
    i ≫ mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ)
          (Sheaf.H.map t 2 x).hom ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map r)⟦(2 : ℤ)⟧' =
      (i ≫ mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ) x.hom ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map u)⟦(2 : ℤ)⟧') ≫
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map v)⟦(2 : ℤ)⟧' := by
  have hx : (Sheaf.H.map t 2 x).hom =
      x.hom ≫ ((DerivedCategory.singleFunctor _ 0).map t)⟦(2 : ℤ)⟧' := by
    simp only [Sheaf.H.map_apply, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    rfl
  rw [hx, mapSingleArrow_postcomp]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, h, Functor.map_comp, Functor.map_comp]

end AlgebraicGeometry.ProEtale.SpTowerClasses
