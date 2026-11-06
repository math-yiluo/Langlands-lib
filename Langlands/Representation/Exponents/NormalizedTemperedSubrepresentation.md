# Normalized-exponent temperedness passes to subrepresentations

This internal supporting result implements the subrepresentation step used in
Renard, *Représentations des groupes réductifs p-adiques*, version of 9 July
2026, VII.2.6, Theorem, printed page 231 / PDF page 237. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`.

`normalizedTemperedSubrepresentation` proves the complete uniform
`NormalizedTemperedSubrepresentationStatement`, by applying the pointwise theorem
`IsNormalizedExponentTempered.of_injective`. Its more general form,
`IsNormalizedExponentTempered.of_injective_intertwining`, allows the source and
target carriers to lie in independent universes. This is needed when the target
is a normalized induction, whose carrier lies in `Type (max u v)`, while the
original representation lies in `Type v`. An injective smooth intertwiner into
a normalized-exponent tempered representation makes its source tempered. The
result does not assume irreducibility. It retains the actual rational-point
topology, every actual parabolic, rational Levi and split component, and the
published normalized-exponent predicate.

The proof first inherits admissibility through the injective intertwiner.
For each actual parabolic triple, the target's temperedness supplies nonempty
compatible root presentations. A chosen presentation identifies the image of any
matching geometric radical with the dynamic unipotent subgroup attached to its
split-component cocharacter. The published dynamic compact-open containment
theorem and its Jacquet adapter then give compact-subgroup containment for that
radical. Consequently the actual normalized Jacquet map is injective. The
cross-universe map `jacquetIntertwining` applies the existing localization map
and then twists it by the same inverse half Haar modulus as the published
Jacquet functor; twisting leaves its underlying linear map unchanged.

The Jacquet intertwiner preserves the generalized weight spaces. Injectivity
preserves their nontriviality, and the character's open-kernel condition is
unchanged. Thus each source exponent is a target exponent and satisfies the
same root-cone condition. The source inherits presentation coverage as well.

The supporting lemmas expose the radical containment and exponent transport
steps. The first uses a compatible presentation; the final temperedness theorem
needs no additional presentation-existence or compact-exhaustion premise because
it obtains the presentation from the target's existing temperedness hypothesis.
The equivalence corollary `isNormalizedExponentTempered_equiv_iff` applies
cross-universe injective closure to the two directions of an actual
representation equivalence. These are derived implementation lemmas, rather than separate numbered
assertions of the source. They do not prove the discrete-series existence,
uniqueness or unitarizability assertions of VII.2.6.
