/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite

/-! # The finite Kummer sequence comparison

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-kummer-sequence-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- The morphism from the etale Kummer sequence after exact site comparison
into the evaluated tower Kummer sequence. Source: Stacks 03PL; Cartier comparison
(blueprint: def-sfb-finite-kummer-sequence-comparison). -/
def finiteKummerSequenceComparison (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) :
    (T.kummerSequence (l ^ (n + 1))).map
        (comparisonUpperStar AddCommGrpCat.{u + 1} T) ⟶
      (ShortComplex.mk k.inclusion k.power k.zero).map (abEvaluation T n) :=
  { τ₁ := cartierRootsComparison T (l ^ (n + 1))
    τ₂ := cartierUnitsComparison T
    τ₃ := cartierUnitsComparison T
    comm₁₂ := by
      change cartierRootsComparison T (l ^ (n + 1)) ≫ k.inclusion.app (op n) = _
      rw [k.inclusion_eq n]
      unfold cartierRootsComparison
      exact kernel.lift_ι _ _ _
    comm₂₃ := by
      change cartierUnitsComparison T ≫ k.power.app (op n) = _
      rw [k.power_eq n]
      change cartierUnitsComparison T ≫ Scheme.proEtaleUnitsPower T (l ^ (n + 1)) =
        (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
          ((l ^ (n + 1)) • 𝟙 T.gmSheaf) ≫ cartierUnitsComparison T
      rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
      simp only [Scheme.proEtaleUnitsPower, Preadditive.nsmul_comp,
        Preadditive.comp_nsmul, Category.id_comp]
      exact Category.comp_id ((l ^ (n + 1)) • cartierUnitsComparison T) }

end AlgebraicGeometry.ProEtale.SpTowerClasses
