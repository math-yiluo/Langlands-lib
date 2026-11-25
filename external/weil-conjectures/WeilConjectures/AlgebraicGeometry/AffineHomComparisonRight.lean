/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineHomComparisonGeneratorExtension

/-! # Covariant naturality of the affine Hom comparison

Source: Stacks Project, Tag 01HV (4)-(5), and Tag 0BQZ.
(blueprint: lem-sc-k4-affine-hom-comparison-right). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Generator normalization implies this affine comparison property.
Source: Stacks Project, Tag 01HV (4)-(5).
(blueprint: lem-sc-k4-affine-hom-comparison-right).

Proof: Precompose the desired equation with each global generator h of
Hom_A(M,N). Generator normalization and functoriality identify its two sides
with the section corresponding to T(h ≫ g). The internal-Hom section
correspondence respects composition. The chart's tilde adjunction detects
maps from an associated module on all its global generators, so the two
maps agree. No finite-presentation or quasi-coherence assumption on internal
Hom is used, and zero rings and zero modules are included. -/
theorem affineHomComparison_chart_right {Y : Scheme.{u}} (U : Y.affineOpens)
    :
    ∀ (M N N' : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (g : N ⟶ N'),
        (affineHomComparison U) M N ≫ SheafOfModules.homObjMap (R :=
          U.1.toScheme.toRingedSpace.sheaf)
          (𝟙 ((affineHomComparisonFunctor U).obj M)) ((affineHomComparisonFunctor U).map g) =
        (affineHomComparisonFunctor U).map (ModuleCat.ofHom (Linear.rightComp (Γ(Y, U.1) : Type u)
          M g)) ≫ (affineHomComparison U) M N' := by
  intro M N N' g
  apply affineHomGenerator_ext U (ModuleCat.of Γ(Y, U.1) (M ⟶ N))
  intro h
  rw [← Category.assoc, affineHomComparison_generator]
  rw [affineHomSection_comp (R := U.1.toScheme.toRingedSpace.sheaf)
    ((affineHomComparisonFunctor U).map h)
    (𝟙 ((affineHomComparisonFunctor U).obj M)) ((affineHomComparisonFunctor U).map g)]
  rw [Category.id_comp, ← Functor.map_comp]
  rw [← Category.assoc, affineHomGenerator_map, affineHomComparison_generator]
  rfl

end AlgebraicGeometry
