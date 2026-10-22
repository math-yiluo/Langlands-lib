# Restriction on exact virtual representations

Author: Worker 20.

This module constructs restriction on the actual exact-sequence Grothendieck
groups of finite-dimensional representations. It supplies the transport needed
to compare representations on isomorphic Weil groups and to move a
representation to the range of a finite-extension embedding before induction.
No reciprocity map, field embedding, or local constant system is assumed to
exist or selected here.

## Underlying construction

For a field `K`, monoids `G` and `H`, and a homomorphism `φ : H →* G`,
the published `FiniteRepresentation.restrict φ A` retains the vector space
of `A` and precomposes its action by `φ`. The source group, target group,
and carrier have independent universes.

`FiniteRepresentation.restrictMap` retains an intertwiner's linear map and
checks its equivariance at `φ h`. The source and target representation
carriers may have different universes. `isShortExact_restrict_iff` is
definitional: injectivity, surjectivity, and equality of image and kernel
are unchanged because all underlying maps are unchanged. `rank_restrict`
is also definitional. `restrictIdEquiv` and `restrictCompEquiv` are the
identity linear equivalence on the retained carrier.

## Descent to the exact quotient

Let `P` and `Q` be predicates on representations of `G` and `H`, with the
same coefficient field and carrier universe. Suppose the explicit closure
implication `P A → Q (restrict φ A)` holds.

- `restrictClassWith` maps genuine isomorphism classes by restriction,
  using the published `restrictEquiv` to verify independence of a
  representative.
- `restrictClassWith_isExactAdditive` sends each actual short exact
  sequence to a short exact sequence and then uses the defining relation
  of the target exact quotient.
- `ExactGrothendieckGroup.restrict` is the resulting integer-linear map
  provided by the published exact-quotient universal property.
- `restrict_ofClass` and `restrict_ofRepresentation` identify its values
  on generators with the classes of the actual restricted representations.
- `degree_comp_restrict` and `degree_restrict` prove preservation of
  virtual dimension by checking genuine generators. `restrictDegreeZero`
  restricts this map to the actual kernels of virtual dimension.
- `restrict_id` and `restrict_comp` prove identity and contravariant
  composition laws. The proof checks generators and uses the actual
  representation equivalences above. The supplied property-closure proofs
  need not be definitionally the same.

These constructions do not replace the exact quotient by the free lattice
or split completion. All original short exact relations are respected.
For arbitrary predicates the source and target remain precisely the
published quotients; no exact-category closure theorem is presumed.

## Continuous representations

For topological groups as group carriers, the topology is an arbitrary
`TopologicalSpace`; continuity of the group operations is not needed for
this restriction construction. The coefficient field is `ℂ` with its usual
topology, and continuity of a representation means continuity into the
module topology on its finite-dimensional endomorphism space.

The published `FiniteRepresentation.isContinuous_restrict` from
`Langlands.Weil.Representation.InductionContinuity` proves closure under a
continuous group homomorphism by composition. The original and restricted
representations have the same endomorphism space and topology.
`continuousRestrict` specializes the descended map using this proved
closure implication. `degree_continuousRestrict` specializes dimension
preservation.

For `e : H ≃ₜ* G`, `continuousRestrictEquivalence` constructs the
integer-linear equivalence from the continuous exact virtual group of `G`
to that of `H`. Its inverse restricts along `e.symm`. Both inverse laws are
proved on generators: the identity linear map intertwines the twice
restricted action with the original action because `e` and `e.symm`
cancel. This proves actual transport, without requiring a classification,
semisimplicity, or a decomposition into characters.

## Provenance and scope

This is a derived construction from the published
`Langlands.Weil.Representation.Restriction`,
`Langlands.Weil.Representation.Predicates`, and
`Langlands.Weil.Representation.InductionContinuity`, together with
`Langlands.VirtualRepresentation.Exact` interfaces. The representation
restriction uses Mathlib's `Rep.res` in
`Mathlib/RepresentationTheory/Rep/Res.lean`, at the project's pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`; its carrier and action formulas
are the ones used here. The new exact virtual maps follow from the
published universal property and the retained linear maps, with the
intrinsic proofs described above. No external arithmetic theorem is
attributed to this algebraic construction.

The module constructs neither induction continuity nor the comparison of
Weil groups attached to distinct field realizations. Those can use these
restriction maps once their actual continuous homomorphisms are supplied.
It introduces no nonabelian epsilon values or existence theorem.
