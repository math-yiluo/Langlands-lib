# Simple-root component coordinates on pinned charts with root-generated characters

This module supplies the adjoint input for the generic component-centralizer factor step
`Langlands.GroupScheme.RootComponentCoordinates` (module
`Langlands.GroupScheme.Reductive.RootComponentCentralizerFactors`).

## Content

Let `M : AffinePinnedModel` be a pinned affine split reductive chart with character lattice
`M.coordinates → ℤ`, full root datum `M.rootDatum` and pinning base `M.basis`. Assume
`hspan : M.rootDatum.rootSpan ℤ = ⊤`, so the roots generate the whole character lattice. This
is the integral lattice form of adjointness for a pinned chart. This module uses only the lattice
condition and makes no claim about fibres.

`AffinePinnedModel.adjointRootComponentCoordinates M hspan : RootComponentCoordinates M` has
these fields:

- `characters` is `simpleRootCoordinates M.basis hspan`, the coefficients of a character in the
  basis of simple roots;
- `rootComponent` is `rootComponent M.basis hspan`, the unique Cartan component of the pinning
  base that supports the simple-root coefficients of a root;
- `root_support` is `simpleRootCoordinates_root_eq_zero`: the coefficients of a root vanish
  outside its component;
- `simple_component` is `rootComponent_simple`: a simple root lies in the component of its own
  index.

The root datum of a pinned chart is reduced (`M.fibrewiseRootDatum.isReduced`) and has finitely
many roots, which the component lemmas require. All of these lemmas are in
`Langlands.LinearAlgebra.AdjointCartanComponents`.

The theorems `adjointRootComponentCoordinates_characters_apply`,
`adjointRootComponentCoordinates_root_self` and `adjointRootComponentCoordinates_root_of_ne`
evaluate the coordinates on characters and on simple roots.

## Provenance

This is internal. It plays the same role as `AffineSimplyConnectedPinnedModel.rootComponentCoordinates`
in the simply connected case, with simple roots in place of simple coroots. For the source, Conrad,
*Reductive group schemes* (2014), Remark 6.4.5 (p. 233), says the proof of Proposition 6.4.4
applies to adjoint groups because an adjoint root datum is a direct product of irreducible ones.
Here the product decomposition of the character lattice is given by the simple-root coordinates
grouped by Cartan component.
