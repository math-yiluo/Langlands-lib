# Generic model socle occurrence in normalized upper induction

Authors: Worker 654, with Worker 181 contributing the accompanying
`Whittaker.CoefficientMapNonvanishing` module and checking the statement's
import closure.

`Langlands.RankinSelberg.twoBlockModelGenericSocleOccurrence.{uF,uV}` proves
exactly the published closed proposition
`Langlands.RankinSelberg.TwoBlockModelGenericSocleOccurrenceStatement.{uF,uV}`.
The field universe and the original dependent carrier universe remain
independent. The original blocks can be reducible, and the theorem retains
every specified nonzero block and induced functional and all four supplied
socle clauses. The target pair and its imported pairs are unchanged.

The implemented proof works directly with actual canonical normalized upper
induction of the complete ordered two-block family. Write `I` for induction
of the original blocks, `K` for induction of their actual coefficient-model
representations, and `J` for induction of the specified block socles. These
three representations retain their actual carriers.

First, the published `normalizedProductModelMap` induces the canonical block
coefficient quotient maps to give `q : I → K`.
`normalizedProductModelMap_surjective` proves its surjectivity using the
smoothness of the original full Whittaker-type blocks. Each specified block
socle has its actual inclusion into its block coefficient model. Inducing
these inclusions gives `j : J → K`. The internal lemma
`ModelSocleOccurrence.tensor_subtype_injective` proves that the external
tensor of these inclusions is injective: over the field of complex numbers,
choose linear retractions of the inclusions and tensor the retractions to
obtain a left inverse. Evaluation of induced functions then proves that
`j` itself is injective. This uses actual induced maps in the given order.

The rest of the argument is packaged in the internal generic-carrier lemma
`ModelSocleOccurrence.subquotient_of_common_quotient`. Full Whittaker type of
`I` and `J` follows from the published `normalizedProductWhittakerType`,
applied respectively to the original blocks and to the specified socles.
The linear equivalence of the entire functional space of `J` with the
complex scalars supplies a nonzero functional by taking the inverse image
of `1`. The representation `K` is smooth by
`TopologicalData.isSmooth_normalizedProductInduced`. The upper unipotent
group is a limit of compact subgroups by the published p-adic containment
theorem. Local constancy of its standard character follows from smoothness
of `I` and its specified nonzero functional. Thus
`functionalsComap_surjective_of_smooth` extends the nonzero functional from
`J` along `j` to a functional on `K`. The extension is nonzero because its
restriction is nonzero.

The published
`coefficientModel_eq_of_surjective_of_whittakerType` compares this extended
functional on `K` with the specified functional on `I`, using the surjection
`q` and full Whittaker type of `I`. It identifies their actual invariant
coefficient images as subrepresentations of the same equivariant-function
representation. It requires no equivalence of either original carrier with
its coefficient model.

Worker 181's helper `coefficientMapCompToSubrepresentation` now gives an
intertwiner from `J` into the specified coefficient model of `I`: precompose
the coefficient map of the extended functional with `j`, and restrict its
codomain using that equality of coefficient models. Its range is nonzero
by `coefficientMapCompToSubrepresentation_range_ne_bot`. The helper proves
nonvanishing by evaluating at the identity; a zero coefficient map would
force the restricted functional to vanish. The supplied least-subspace
clause for `S` therefore places `S` inside this nonzero invariant range.
Finally, `ModelSocleOccurrence.subquotient_of_le_range` defines the actual
invariant subspace `A` of `J` as the inverse image of `S`, restricts the
intertwiner to `A → S`, and uses the range inclusion to prove surjectivity.
These are the witnesses required by the target.

The three `ModelSocleOccurrence` lemmas and the coefficient-map helper are
internal algebraic derivations from the named Library and Mathlib maps and
theorems. The proof uses the full-type clauses for the block socles and the
least-subspace clause for `S`; the other supplied socle clauses remain in the
exact proposition. It adds no finite-length, classification, analytic, or
constituent-occurrence assumption.

The literature motivation is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), Section 5.4, printed page 423, between
equations (3) and (4). Sections 2.1–2.3, printed pages 385–387, supply the
full-type, coefficient-image, and heredity conventions. This direct upper
induction proof has a different route from the source's lower induction
convention; it does not invoke a lower-to-upper comparison. The registered
source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 654 visually read those four printed pages and verified the original
fingerprint on 2026-11-01. A bounded check of the literature index and
project and Library notes found no registered source-specific JPSS errata.
The accompanying helper's Markdown records Worker 181's source reading and
its direct algebraic provenance.
