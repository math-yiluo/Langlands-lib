# Natural inner corrections of comparisons of pinned models

The theorem `Langlands.GroupScheme.relativePinnedComparisonExistence` proves
the unchanged `RelativePinnedComparisonExistenceStatement.{u}` in every
universe, with no additional hypotheses.

It supplies a comparison operation on actual isomorphisms between pullbacks
of the given affine pinned split reductive models to an arbitrary common
scheme. The operation preserves identities and composition, commutes with
arbitrary pullback through the specified normalized comparison maps, and
preserves the actual coordinate torus inclusions and canonical positive-coroot
cocharacters. For every supplied fppf quotient by the full centre and every
supplied compatible conjugation action, the discrepancy between an original
comparison and its corrected comparison is the action of a global section
of that quotient.

Common schemes and refinements may be disconnected, nonaffine, empty, or not
quasi-compact. Outer classes may vary locally. The proof adds no connectedness,
locality, nontriviality, affine-cover restriction, or choice of a fixed global
root relabelling.

The implemented proof assembles the already established geometric existence,
inner rigidity, all-test independence, and descent results:

1. `fppfLocalPinnedNormalizationExistence` constructs a single actual fppf
   cover and a concretely pinned comparison on it, together with an actual
   source section whose inner automorphism is exactly the discrepancy.
   Its construction combines affine etale based-normalization charts with
   actual inverse-simple-root unit corrections and cover assembly.
2. `hasFppfLocalPinnedRepresentatives_of_localNormalization` converts this
   geometric statement into `HasFppfLocalPinnedRepresentatives`. Concrete
   pinning gives its fppf-local predicate using the identity cover. An actual
   inner automorphism is fppf-locally inner: on the identity cover its defining
   conjugation equation holds on every relative test. Substitution of the
   supplied source-discrepancy equation proves the required inner equivalence.
   The theorem `AffinePinnedModel.hasFppfLocalPinnedRepresentatives` applies
   this conversion to the unconditional geometric theorem.
3. `relativePinnedComparisonExistence_of_localPinnedRepresentatives` applies
   the proved rigidity and independence results to those local representatives,
   descends the unique normalized representatives, and obtains their identity,
   composition, arbitrary-pullback, torus and cocharacter laws from uniqueness
   and the local geometric laws. Its existing adjoint-section construction
   descends representatives in every supplied quotient by the full centre
   with its supplied action.

The final theorem is exactly the application in step 3 to the input proved in
step 2. The target statement and its imported definitions are unchanged. This
file proves the Library formulation motivated by Conrad's pinned isomorphism
and automorphism-splitting results; its implemented proof route is the explicit
geometric correction, rigidity, independence and descent construction described
above.
