# Isomorphism invariance of complex representation predicates

Worker 16 proves the existing Library proposition
`Langlands.Weil.RepresentationIsomorphismInvariance.{uG,uV,uU}` with the closing
theorem `Langlands.Weil.representationIsomorphismInvariance`. The statement in
`Operations.lean` and its Markdown, and every imported definition, are unchanged.

The theorem takes an arbitrary group with an arbitrary topology, an arbitrary
subgroup, and finite-dimensional complex representations on independently
universed carriers. It extracts the actual invertible linear intertwiner from
`Nonempty (ρ.Equiv σ)`. No compatibility of the group topology with multiplication,
normality or openness of inertia, positive dimension, finiteness of either image,
or semisimplicity is assumed. Zero-dimensional carriers are included.

## Implemented proof

Mathlib's `Representation.Equiv.conj_apply_self` identifies each action of `σ`
with conjugation of the corresponding action of `ρ` by the supplied equivalence.
The reusable comparisons in `Langlands.Weil.IsomorphismInvariance` implement the
following steps:

- `action_eq_one_iff` uses the injectivity and identity preservation of
  `LinearEquiv.conjRingEquiv`. Extensionality gives `ker_eq` and
  `restricted_ker_eq`. Equality of the restricted kernels directly gives
  equivalence of their openness. Applying the pointwise identity equivalence
  to every inertia element gives equivalence of trivial inertia action.
- `finite_range_comp_iff` identifies the image after any function into the group
  with the image of the original range under the injective conjugation map.
  `Set.finite_image_iff` then proves equivalence of finiteness. The closing
  theorem uses the identity function for the whole group and the subgroup
  inclusion for inertia.
- `continuous_of_equiv` treats conjugation as a linear map of endomorphism
  spaces. `IsModuleTopology.continuous_of_linearMap` makes it continuous for
  the canonical complex module topologies. Composition and the pointwise
  conjugacy identity give continuity of the transported action.
  `continuous_iff` applies this to the equivalence and its inverse. These
  helpers require no finite-dimensionality or topological-group instance.
- `irreducible_iff` and `semisimple_iff` use Mathlib's identifications with
  simplicity and semisimplicity of the group-algebra module. The existing
  `IntertwiningMap.equivLinearMapAsModule` converts the supplied intertwiner
  into a group-algebra linear map with the same underlying bijective function.
  The bijective-module comparison theorems transport both properties.
- The dimension clause reuses `FiniteRepresentation.rank_eq_of_equiv` on
  `FiniteRepresentation.of ρ` and `FiniteRepresentation.of σ`. The determinant
  clause evaluates the published equality
  `FiniteRepresentation.determinantCharacter_eq` at each group element and
  then takes its scalar value. Both existing comparisons support independent
  carrier universes and rank zero.

The closing proof assembles precisely the eleven existing conjuncts, without
changing their predicates or supplying additional hypotheses. No basis,
classification, decomposition, or conjugacy witness beyond the actual input
representation equivalence is assumed.

## Provenance and verification

This is a derived proof of the published target, whose source rationale and
original-literature correspondence are documented in `Operations.md`: change
of representation by an invertible intertwiner preserves its intrinsic
properties. The implementation uses the pinned Mathlib conjugation,
group-algebra-module, and module-topology APIs, together with the published
`Basic` and `Determinant` comparisons; it introduces no new source claim or
competing representation bundle.

Development validation uses environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The closing declaration is checked
unapplied against both the existing proposition and its complete expanded
quantifier telescope, with independent `uG`, `uV`, and `uU`. Declaration
inspection checks that the only axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Development checks do not replace the candidate's machine
exact-target validation, independent semantic review, or Library publication.
