# Model existence for quasi-separated algebraic spaces along affine limits

Author: Worker 116.

`Langlands.AlgebraicGeometry.AlgebraicSpace.spaceLimitModelExistenceQuasiSeparated`
proves the unchanged Library proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistenceQuasiSeparated`
in every universe `u`.

The proof applies the published theorem
`SpaceLimitModelExistenceQuasiSeparatedReduction.spaceLimitModelExistenceQuasiSeparated_of_relation`
to the published scheme theorem
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.limitModelExistence`.
The latter proves `EtaleEquivalenceRelation.LimitModelExistence`, so it supplies
the explicit scheme-relation descent input of the reduction.

For an arbitrary small cofiltered diagram of affine schemes with an actual
limit cone, the reduction constructs a finite affine étale presentation of the
given quasi-separated algebraic space. The scheme theorem descends the object
scheme, relation scheme, projections, equivalence laws and étaleness to a common
stage. The reduction forms the quasi-separated quotient at that stage, retains
its quasi-compact locally finitely presented atlas, and identifies its actual
base change with the original space using the common represented kernel pair.
Extracting the resulting stage, space, two finiteness properties and
base-change isomorphism gives exactly the target conclusion.

This composition adds no hypotheses. In particular, the input space need only
be quasi-separated, the relation scheme need not be affine, and the indexing
category is any small cofiltered category in the stated universe. The statement
and its imports are unchanged.

The target records the model-existence part of Conrad's Theorem 3.4(1) for
algebraic spaces, asserted on printed p.13 of *Weil and Grothendieck approaches
to adelic points*. The presentation, scheme descent and quotient route is the
one implemented in the two imported developments and explained in their paired
Markdown, following Stacks Project Lemma 70.7.1 (Tag 07SK). This file supplies
the final composition of those results.
