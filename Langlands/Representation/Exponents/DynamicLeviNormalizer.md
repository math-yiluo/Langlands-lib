# Normalizers of rational Levis with a supplied dynamic presentation

Author: Worker 1739.

This internal adapter concerns an original rational parabolic `p : P → G`
of a connected reductive group over an arbitrary field and its original
rational Levi `l : M → P`. It takes a single supplied cocharacter `χ` whose
dynamic parabolic is represented by that same `p`.

`IsRationalLeviSubgroup.exists_finite_normalizer_representatives_of_dynamicParabolic`
constructs a natural number `n` and points `g : Fin n → G(k)`. Each `g t`
normalizes the original Levi through an actual group-scheme automorphism of
`M`. Every rational point `w` normalizing that Levi is
`g t * rationalPoints.map (l ≫ p) m` for some index `t` and actual point
`m : M(k)`. This theorem does not use a valuation or topology.

The proof chooses a split component using `splitComponentStatement`.
The published
`IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
identifies the centralizer of that whole split component, on every test
scheme, with the original Levi image. Connected reductivity supplies the
affineness and finite-type hypotheses, and the original Levi and parabolic
maps supply closedness. Applying
`IsSplitComponent.exists_finite_normalizer_representatives` gives the
asserted right-coset factorizations.

`IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic` chooses
the finite family together with its length as a dependent pair. Its `_spec`
theorem records both the normalizing automorphisms and the factorization
property.

Over a nonarchimedean local field,
`IsRationalLeviSubgroup.mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic`
proves the norm-fixing consequence for the original Levi. Its hypothesis
compares every rational-character norm before and after the supplied
normalizing automorphism on every point of the abstract center of `M(k)`.
Using the same split-component centralizer equality,
`IsSplitComponent.mem_range_of_normalizes_of_norm` gives membership in the
actual rational-point range. `pointImage_eq_range_carrier` identifies this
range with the literal Levi image.

The provenance is the displayed composition of existing Library results
and the normalizer helpers. No additional external assertion is used.
Existence of the initial dynamic presentation remains an explicit input.
These results do not prove a dynamic presentation for an arbitrary rational
parabolic or the closed generic-irreducibility theorem.
