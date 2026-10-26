# Cancellation for a tensor of morphisms from the unit

Authors: Worker 370 and Worker 124. Worker 124 supplied the interface and the categorical derivation.

`Langlands.CategoryTheory.Picard.UnitTensorCancellationStatement C` is the proposition that, for all objects `M`, `N` of a braided monoidal category `C` and morphisms `s : 𝟙_ C ⟶ M`, `t : 𝟙_ C ⟶ N`, the hypothesis `IsIso (s ⊗ₘ t)` implies `IsIso s ∧ IsIso t`. The object universe `u` and morphism universe `v` are arbitrary and independent. The only ambient assumptions are `Category.{v} C`, `MonoidalCategory C` and `BraidedCategory C`.

The source and target of the tensor morphism are `𝟙_ C ⊗ 𝟙_ C` and `M ⊗ N`. Neither individual morphism nor either target object is assumed invertible. The statement requires no balancedness, abelian structure, additive structure, closed structure, or module or sheaf hypothesis. It imports the existing `Langlands.CategoryTheory.Picard.TensorEquivalenceStatement` without changing that module.

## Internal derivation and intended use

This is an internal categorical prerequisite for a direct unit-pairing route to the converse in Stacks Project Lemma 17.25.4. The source does not state this generalization to arbitrary braided monoidal categories.

The proposed categorical argument starts with an isomorphism `g = s ⊗ₘ t`. Its inverse, followed by the unitor `𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C`, supplies an isomorphism `M ⊗ N ≅ 𝟙_ C`. Thus `N` is a right tensor inverse of `M`; the braiding also supplies `N ⊗ M ≅ 𝟙_ C`. In particular, tensor-invertibility of both objects is a consequence of the hypothesis. The existing theorem `Langlands.CategoryTheory.Picard.tensorInvertibilityEquivalence` in `Langlands.CategoryTheory.Picard.TensorEquivalenceProof` then makes left tensoring by `N` an equivalence. Braiding identifies right tensoring by `N` with left tensoring by `N`, so right tensoring by `N` is also an equivalence.

Functoriality of tensor gives both factorizations

```text
g = (s ⊗ₘ 𝟙 (𝟙_ C)) ≫ (𝟙 M ⊗ₘ t)
  = (𝟙 (𝟙_ C) ⊗ₘ t) ≫ (s ⊗ₘ 𝟙 N).
```

The first factor of an invertible composite is a split monomorphism, so the first factorization makes `s ⊗ₘ 𝟙 (𝟙_ C)` a split monomorphism. Right tensoring by the unit is naturally isomorphic to the identity and reflects splittings; hence `s` is a split monomorphism. The last factor of an invertible composite is an epimorphism, so the second factorization makes `s ⊗ₘ 𝟙 N` an epimorphism. Right tensoring by `N`, being an equivalence, reflects epimorphisms; hence `s` is an epimorphism. A split monomorphism that is an epimorphism is an isomorphism in any category. Naturality of the braiding transfers invertibility of `s ⊗ₘ t` to `t ⊗ₘ s`, and the same argument gives invertibility of `t`.

This file only defines the proposition. The argument above describes the intended derivation for a separate proof contribution; it is not an implemented Lean proof. A geometric application must still construct the local factorization into morphisms from the unit and show their tensor is invertible. Neither the ringed-space converse nor a scheme-specific local factorization is asserted here.

## Source and scope

In the retained original, Definition 17.25.1 defines an invertible module on a ringed space by equivalence of left tensoring. Lemma 17.25.2 identifies this with existence of a tensor inverse; its first proof paragraph constructs the quasi-inverse functor. Its remaining proof establishes local finite-projective behavior and the internal-Hom description. Lemma 17.25.4 states that locally free modules of rank one are invertible and proves the converse when all stalk rings are local. Its converse proof uses invertibility of stalk modules and finite presentation. The categorical cancellation statement and the proposed direct unit-pairing route above are internal developments, not claims that the source gives that proof.

Source: The Stacks Project Authors, *The Stacks Project*, Section 17.25, retained `01CR.html`, Definition 17.25.1, Lemma 17.25.2 with proof, and Lemma 17.25.4 with proof. Registered source `stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256 `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`, HTML snapshot 2026-10-21. Retained folder: `literature/Stacks Project - Locally free sheaves and invertible modules, Sections 17.14 and 17.25 (HTML snapshot 2026-10-21)/`. These passages were read. On 2026-10-26, no source-specific errata file was present in the supplied current Library notes or project notes.
