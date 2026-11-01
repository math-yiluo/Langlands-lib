# Exact finite-length K0 under continuous group equivalence

Author: Worker 320.

This internal construction applies the published exact Grothendieck functor to
the published smooth pullback functor. For groups with arbitrary topologies and
a continuous multiplicative equivalence `e : H ≃ₜ* G`, it constructs an
integer-linear equivalence from the exact finite-length smooth complex K0 of
`G` to that of `H`. The group universes and the common representation carrier
universe are independent.

The action on an actual representation is `h ↦ ρ (e h)`. Surjectivity of `e`
allows the published `finiteLength_comp_surjective_iff` to transfer finite
group-algebra length. Pullback retains every underlying linear map. Thus
injectivity, surjectivity, and equality of image and kernel in an actual short
exact sequence are retained. These facts supply both hypotheses of the generic
exact K0 map. The quotient retains all actual short exact relations.

`FiniteLengthGrothendieckGroup.pullback` is that map, and
`pullback_ofRepresentation` computes it on the literal smooth pullback for any
finite-length proof of the output. `pullback_refl`, `pullback_trans`, and
`pullback_symm_comp` follow by equality on finite-length object generators.
The comparisons have the identity linear equivalence. Their action equations
are definitional for identity and composition, and use `e (e.symm g) = g` for
the inverse. Composition is contravariant: for `f : J ≃ₜ* H`, pullback by
`f.trans e` equals pullback by `e` followed by pullback by `f`.

`pullbackEquiv` packages the map with inverse pullback by `e.symm`.
Its forward linear map and its inverse equivalence have the displayed
definitional formulas. This construction requires no admissibility,
irreducibility, compact support, finite vector-space dimension, or continuity of
the group operations. The imported compact-coefficient module supplies the
actual smooth pullback functor; its compact-coefficient predicates are unused.

The provenance is the explicit internal derivation above. No new theorem from
original literature is transcribed. The construction changes the acting group
along a supplied equivalence and asserts no compatibility with induction,
Jacquet restriction, an Aubert operator, or analytic classification.
