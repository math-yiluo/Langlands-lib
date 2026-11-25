/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveSystemEmbedding

/-! # Injective embeddings of coefficient systems

Source: Stacks Project, Tags 0EXZ and 04JC.
(blueprint: lem-weil-pbc-etale-coefficient-injective-system).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- A compatible coefficient system admits a compatible stagewise injective embedding.
Source: Stacks Project, Tag 0EXZ, product of direct images over all outgoing arrows.
(blueprint: lem-weil-pbc-etale-coefficient-injective-system).

Proof: Choose the canonical embedding of each F k into Injective.under (F k).
At i take the product of their direct images over pairs (k, f : i to k).
The component of ai at f is the adjoint of φ f followed by the embedding at k.
The identity component is monic and therefore ai is monic. Direct image
preserves injectives because its left adjoint is exact; products of injectives
are injective. For f : i to j define ψ f componentwise at g : j to k by the
projection to the factor indexed by f followed by g, followed by the canonical
counit comparison from inverse image of that direct image to the direct image
indexed by g. The composition comparison for direct image identifies these
maps. Check product projections and transpose across the adjunction: the
adjunction unit and counit equations and associativity of inverse-image
comparisons give identity and composition, and hcomposition gives compatibility
with ai. No cone point, cokernel or exact functor-category diagram is asserted. -/
theorem etale_coefficient_injective_system
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
 :
    ∃ (FI : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FI i) ⟶ FI j)
    (hidentityI : ∀ i : I, ψ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FI i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FI i))
    (hcompositionI : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ψ f) ≫ ψ g)
    (ai : ∀ i : I, F i ⟶ FI i),
      (∀ i : I, Injective (FI i)) ∧ (∀ i : I, Mono (ai i)) ∧
      (∀ (i j : I) (f : i ⟶ j),
        φ f ≫ ai j = (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).map (ai i) ≫ ψ f)
    := by
  obtain ⟨ψ, hidentityI, hcompositionI, ai, hmono, hacompat⟩ :=
    etale_coefficient_injective_system_embedding D F φ hidentity hcomposition
  exact ⟨etaleCoefficientInjectiveTarget D F, ψ, hidentityI, hcompositionI, ai,
    etale_coefficient_injective_system_data D F, hmono, hacompat⟩

end AlgebraicGeometry.Etale
