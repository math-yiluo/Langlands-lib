# Relative pure fibre dimension and etale scheme charts

Author: Worker 156.

`PureFibreDimensionMorphismProperty d` is the conjunction of local finite type
and the published componentwise pure dimension `d` of every actual
residue-field fibre of a scheme morphism. Every irreducible component of each
fibre must have topological Krull dimension `d`; empty fibres satisfy this
condition vacuously. The property adds no nonemptiness or connectedness
condition.

`EtalePureFibreDimensionComparisonStatement` says that this combined property
is equivalent for `f` and `p ≫ f` when `p` is surjective and étale, and for `f`
and `f ≫ g` when `g` is étale. It quantifies arbitrary schemes in universe
`u`, every natural number `d`, and actual scheme morphisms. There are no
separation, quasi-compactness, field-base or noetherian hypotheses.
`etalePureFibreDimensionComparison` proves both equivalences using the
individual composition and descent lemmas.

For an étale source map, the induced map of actual fibres is a pullback of
that map and hence étale. The published étale comparison of local topological
dimension identifies the relative dimensions at corresponding source points.
Here local topological dimension means the minimum dimension of open
neighbourhoods, as defined in `LocalTopologicalDimension`.

For a locally quasi-finite target map, its point fibres are discrete. The
smaller point fibre of `f` is therefore open in the point fibre of `f ≫ g`,
by pulling back a singleton in this discrete space. Invariance under open
embeddings identifies the relative dimensions. These two pointwise
comparisons require no local-finite-type premise on `f`.

For the combined property, local finite type identifies pure fibre dimension
with constancy of relative local topological dimension. Étale composition
preserves local finite type on both sides; cancellation of the target
composition uses the standard local-finite-type cancellation result.
Surjectivity of the source chart lifts each point, while the published flat,
locally finitely presented source-descent result supplies local finite type
of `f`. These facts prove the four scheme-property callbacks needed for
comparison of arbitrary étale chart squares.

The module also records invariance under isomorphisms and arbitrary scheme
base change for the combined property. Base change uses the published
pure-dimension comparison of locally finite-type actual fibres, together
with stability of local finite type.

This is an internal derivation from `EtaleLocalDimension`,
`SchemePureDimensionProof`, and
`Morphisms.LocallyOfFiniteTypeSourceDescentProof`, using the existing actual
fibre and relative dimension APIs. It is supporting work for the
algebraic-space limit theorem. The algebraic-space chart comparison,
limit-descent assembly, and geometric-connectedness argument remain separate
obligations.
