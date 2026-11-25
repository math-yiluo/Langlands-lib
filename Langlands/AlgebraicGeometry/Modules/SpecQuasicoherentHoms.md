# Morphisms of quasi-coherent modules on an affine spectrum

Let `R` be a commutative ring and let `M`, `N` be quasi-coherent module sheaves
on `Spec R`. Mathlib's `tildeEquiv` is the equivalence between `R`-modules and
quasi-coherent modules on `Spec R`. Its inverse is the global-section functor
`moduleSpecΓFunctor`, restricted to the quasi-coherent full subcategory.

- `homEquiv M N` is the bijection between morphisms `M ⟶ N` and morphisms of
  `R`-modules between their global sections. It composes the full faithfulness
  of the inclusion of the quasi-coherent full subcategory with the full
  faithfulness of the inverse of `tildeEquiv`. `homEquiv_apply` records that it
  sends `φ` to `moduleSpecΓFunctor.map φ`.
- `hom_ext` says that two morphisms `M ⟶ N` agreeing on global sections are
  equal.
- `lift ℓ` is the unique morphism `M ⟶ N` whose map on global sections is a
  given morphism `ℓ` of `R`-modules. `lift_app` states that its value on a
  global section `x` is `ℓ x`.
- `isoOfIso e` lifts an isomorphism `e` of the global-section modules to an
  isomorphism `M ≅ N`. Its two composites are checked to be identities with
  `hom_ext`. `isoOfIso_hom_app` records its action on global sections.

Only quasi-coherence of `M` and `N` is assumed. No finiteness and no
hypothesis on `R` is needed.

## Provenance

This is an internal convenience layer over Mathlib's
`AlgebraicGeometry.tildeEquiv`, the standard equivalence between modules over
`R` and quasi-coherent sheaves on `Spec R`. It rests on the mapping property
of the associated sheaf, Stacks Project, Lemma 26.7.1 (tag 01I7). It is used in the torsion bracket argument for eventual
quasi-projectivity of fine moduli schemes of ordinary polarized full-level data
(module `EvaluationBracketFibres`) to construct
isomorphisms of evaluation data over the spectrum of a field from linear
algebra on global sections.
