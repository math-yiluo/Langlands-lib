/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The product of direct images of the canonical stagewise injective objects.
Source: Stacks Project, Tag 0EXZ, product over outgoing arrows.
(blueprint: def-weil-pbc-etale-coefficient-injective-target). -/
noncomputable def etaleCoefficientInjectiveTarget
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : I) : Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ∏ᶜ fun t : Σ k : I, i ⟶ k ↦
    (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj (Injective.under (F t.1))

/-- The specified product target is injective at every index.
Source: Stacks Project, Tag 0EXZ: exact inverse image, right adjoints and products.
(blueprint: lem-weil-pbc-etale-coefficient-injective-system-data).

Proof: each canonical stage object is injective by enough injectives. The direct
image of each such object is injective because its left adjoint, inverse image,
preserves finite limits and hence monomorphisms. Products of injectives are
injective, so the product over all outgoing arrows is injective. -/
theorem etale_coefficient_injective_system_data
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : I) : Injective (etaleCoefficientInjectiveTarget D F i) := by
  have factors (t : Σ k : I, i ⟶ k) :
      Injective ((lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
        (Injective.under (F t.1))) := by
    let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map t.2.op)
    let := adj.preservesInjectiveObjects_of_preservesFiniteLimits
    exact Functor.injective_obj _ _
  let := factors
  unfold etaleCoefficientInjectiveTarget
  infer_instance
end AlgebraicGeometry.Etale
