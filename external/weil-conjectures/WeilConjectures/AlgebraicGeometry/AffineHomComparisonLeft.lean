/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineHomComparisonGeneratorExtension

/-! # Contravariant naturality of the affine Hom comparison

Source: Stacks Project, Tag 01HV (4)-(5), and Tag 0BQZ.
(blueprint: lem-sc-k4-affine-hom-comparison-left). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Generator normalization implies this affine comparison property.
Source: Stacks Project, Tag 01HV (4)-(5).
(blueprint: lem-sc-k4-affine-hom-comparison-left).

Proof: Precompose the desired equation with each global generator h of
Hom_A(M,N). Generator normalization and functoriality identify its two sides
with the section corresponding to T(f ≫ h). The internal-Hom section
correspondence respects composition. Maps from an associated module are
jointly detected by their global generators: apply the chart's tilde
adjunction and evaluate the adjoint linear maps at every element. This
proves the equation for arbitrary modules, including zero modules and the
zero ring. -/
theorem affineHomComparison_chart_left {Y : Scheme.{u}} (U : Y.affineOpens)
    :
    ∀ (M M' N : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (f : M' ⟶ M),
        (affineHomComparison U) M N ≫ SheafOfModules.homObjMap (R :=
          U.1.toScheme.toRingedSpace.sheaf)
          ((affineHomComparisonFunctor U).map f) (𝟙 ((affineHomComparisonFunctor U).obj N)) =
        (affineHomComparisonFunctor U).map (ModuleCat.ofHom (Linear.leftComp (Γ(Y, U.1) : Type u)
          N f)) ≫ (affineHomComparison U) M' N := by
  intro M M' N f
  apply affineHomGenerator_ext U (ModuleCat.of Γ(Y, U.1) (M ⟶ N))
  intro h
  rw [← Category.assoc, affineHomComparison_generator]
  rw [affineHomSection_comp (R := U.1.toScheme.toRingedSpace.sheaf)
    ((affineHomComparisonFunctor U).map h) ((affineHomComparisonFunctor U).map f)
    (𝟙 ((affineHomComparisonFunctor U).obj N))]
  rw [Category.comp_id, ← Functor.map_comp]
  rw [← Category.assoc, affineHomGenerator_map, affineHomComparison_generator]
  rfl

end AlgebraicGeometry
