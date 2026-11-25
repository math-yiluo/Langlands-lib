# Affine product-units splitting from tensor-product units

This module supplies the coordinate-ring bridge for the product-units theorem.
It defines the fixed-algebra predicate
`Langlands.GroupScheme.UnitsProduct.TensorUnitsSplit.{u,v,w}` and proves that
its domain case implies splitting of morphisms from affine integral varieties
to the actual multiplicative group scheme. The tensor-unit theorem remains an
explicit hypothesis; this module does not prove
`UnitsProductDecompositionStatement` unconditionally.

This is internal infrastructure. Its provenance is the standard affine
coordinate-ring interpretation of a product of schemes and of the represented
units functor, implemented using existing published Library results. The module
imports the unchanged product-units statement, which imports the actual `Gm`
construction, and the published FLT port
`S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage`.
It introduces no new axioms or literature-dependent mathematical assertions.

## Fixed-algebra input

For a commutative base ring `k`, commutative `k`-algebras `A` and `B`, and
independent universes for all three rings, `TensorUnitsSplit k A B` states

```lean
∀ z : (A ⊗[k] B)ˣ, ∃ (a : Aˣ) (b : Bˣ),
  (z : A ⊗[k] B) = (a : A) ⊗ₜ[k] (b : B)
```

This is a `Prop`-valued definition with no assertion that it holds for arbitrary
rings. It allows a theorem for finitely generated domains over an
algebraically closed field (in the Library, `Langlands.Algebra.rosenlichtTensorUnits`)
to be used without importing that theorem here
or introducing an extra premise into the original target statement.

## Implemented bridge

All scheme-level declarations use one universe `u`, as does the original
product-units target. The coordinate rings carry the scalar structures
`Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤` and
`Scheme.TwoAffineOpenCover.algebraOfHom Y.hom ⊤`, induced by their actual
structure morphisms and the canonical identification `Γ(Spec k, ⊤) ≅ k`.

- `exists_affine_product_sections_equiv` applies the published tensor-sections
  equivalence to the two top affine opens. The product open is
  `fst ⁻¹ᵁ ⊤ ⊓ snd ⁻¹ᵁ ⊤ = ⊤`; transport along this equality gives a ring
  equivalence from `Γ(X, ⊤) ⊗[k] Γ(Y, ⊤)` to `Γ(X ×ₖ Y, ⊤)`. Its pure tensor
  formula is the product of the pullbacks along the actual two projections.
- `affine_splitting_of_tensor_units` requires affine schemes over `Spec k`,
  with `k` any commutative ring, and the fixed-algebra predicate for their
  coordinate rings. It transports the global unit of a morphism `f` to the
  tensor product, applies the factorization hypothesis, and uses
  `Gm.pointsEquiv.symm` to construct the two factor morphisms. Injectivity of
  `Gm.pointsEquiv`, its naturality under the two projections, and the pure
  tensor formula prove the required equality of morphisms.
- `finiteType_sections_algebra` proves that the displayed coordinate-ring
  scalar structure is of finite type whenever the affine scheme's structure
  morphism is locally of finite type. It composes the ring-map finite-type
  property supplied by `HasRingHomProperty.appTop` with the inverse of
  `Scheme.ΓSpecIso`; this inverse is surjective because it is an isomorphism.
- `affine_splitting_of_domain_tensor_units` accepts a tensor-unit theorem for
  all finitely generated domains over all algebraically closed fields in
  universe `u`. For affine integral schemes locally of finite type, their
  global sections are domains, and the preceding finite-type lemma supplies
  the remaining hypotheses. It then applies the fixed-algebra bridge.

The final conditional theorem has exactly the affine schemes, integrality,
local-finite-type hypotheses and splitting conclusion required by the separate
geometric reduction. The tensor-unit hypothesis is still required. No
compactification, normality, rational points, or geometric-integrality
certificates are added to that affine conclusion.
