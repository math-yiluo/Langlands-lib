/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors

/-! # A concrete common source prefix

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: def-sbc-raw-module-scalar-source-prefix).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The source comparison followed by the forgotten class, with coefficients unprocessed.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: def-sbc-raw-module-scalar-source-prefix). -/
noncomputable def rawModuleScalarSourcePrefix
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :=
      (abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
        (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
          (scalarSourceFactor Λ (B.hom ≫ k) ((freeSheaf Λ S).obj U)
            (RawModuleScalarComparison.freeAbelian S U)
            (RawModuleScalarComparison.freeMap Λ S U) ≫
            (moduleAbelianForget Λ B.left).mapDerivedCategoryPlus.map z))

end AlgebraicGeometry.Etale
