/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness of a coproduct of two schemes

Source: literature/stacks-project/coherent.tex, proof of Lemma 0CYR; Schemes,
Section 01JA (blueprint: lem-weil-pbc-proper-coproduct).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/--
(blueprint: lem-weil-pbc-proper-coproduct)
For morphisms `p₁ : W₁ ⟶ S` and `p₂ : W₂ ⟶ S`, their coproduct morphism
has the stated open coproduct pieces and is proper when both components are
proper. Source: Stacks, Cohomology of Schemes, proof of Lemma 0CYR
(`lemma-union-closed-proper-over-base`); Schemes, Section 01JA.

Proof, following the four steps of the node:

1. Apply `lem-weil-pbc-scheme-coproduct-family` to the two-element family. The
   coprojections are open immersions and their images `U₁`, `U₂` are disjoint and
   cover the coproduct. Each image is also closed, being the other's complement.
   Each coprojection identifies its source with its open image over `S`.
2. Assume both component maps proper. For every affine open `V` of `S`, choose
   finite affine covers of `p₁ ⁻¹ V` and `p₂ ⁻¹ V` with finitely generated
   coordinate algebras (`def-weil-finite-type-morphism`). Transport these covers
   through the open immersions. Their union covers `p ⁻¹ V`, and the algebra
   structures agree because the component composites equal `p₁` and `p₂`.
   This proves finite type, including quasi-compactness of each inverse image.
3. For any `T ⟶ S`, `lem-weil-pbc-open-fibre-product` identifies the two
   component base changes with the complementary open pieces of the base change
   of the coproduct. For a closed subset `Z` of that base change, its image in
   `T` is the union of the images of its closed inverse images in the two
   components. Each image is closed by universal closedness of the component
   maps (`def-weil-proper-morphism`); their finite union is closed. Thus `p` is
   universally closed.
4. The four pieces `pr₁ ⁻¹ Uₖ ∩ pr₂ ⁻¹ Uₗ` partition `W ×[S] W` into clopen
   subsets. By `lem-weil-pbc-open-fibre-product`, the two equal-index pieces are
   the component self-products. The image of the diagonal of `p` is the union
   of the component diagonal images in these pieces. Each is closed because
   the component map is separated and the piece is closed. The diagonal is an
   immersion (`lem-weil-pbc-diagonal-immersion`), so its closed image makes it a
   closed immersion (`lem-weil-pbc-immersion-closed-image-closed-immersion`).
   Thus `p` is separated; together with steps 2 and 3, this is properness by
   `def-weil-proper-morphism` (Stacks, Morphisms, Definition 01W1).
-/
theorem proper_coproduct_two
    {S W₁ W₂ : Scheme.{u}} (p₁ : W₁ ⟶ S) (p₂ : W₂ ⟶ S) :
    IsOpenImmersion (coprod.inl : W₁ ⟶ W₁ ⨿ W₂) ∧
      IsOpenImmersion (coprod.inr : W₂ ⟶ W₁ ⨿ W₂) ∧
      IsCompl (Set.range (coprod.inl : W₁ ⟶ W₁ ⨿ W₂))
        (Set.range (coprod.inr : W₂ ⟶ W₁ ⨿ W₂)) ∧
      (∀ [IsProper p₁] [IsProper p₂],
        IsProper (coprod.desc p₁ p₂ : W₁ ⨿ W₂ ⟶ S)) := by
  refine ⟨inferInstance, inferInstance, isCompl_range_inl_inr W₁ W₂, ?_⟩
  intro _ _
  have : IsProper (coprod.map p₁ p₂) :=
    IsZariskiLocalAtTarget.coprodMap (P := @IsProper) p₁ p₂ inferInstance inferInstance
  have : IsProper (coprod.desc (𝟙 S) (𝟙 S)) := inferInstance
  have h : coprod.map p₁ p₂ ≫ coprod.desc (𝟙 S) (𝟙 S) = coprod.desc p₁ p₂ := by
    ext <;> simp
  rw [← h]
  infer_instance

end AlgebraicGeometry
