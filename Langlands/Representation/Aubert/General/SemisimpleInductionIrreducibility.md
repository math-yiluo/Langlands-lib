# Irreducibility of semisimple induction detected by its actual Jacquet module

Author: Worker 480.

This internal derived helper treats the published actual normalized induction
and Jacquet functors for a semidirect decomposition `P = M U` of subgroups of
a locally compact nonarchimedean group `G`. The subgroup `U` is closed and
unimodular. The group universe and the inducing carrier universe are independent.

The first lemma proves that every nonzero idempotent endomorphism of the induced
representation is the identity when its actual normalized Jacquet module is
irreducible. Its nonzero first adjoint is injective, because its source is simple.
Naturality of first adjointness applied to the idempotent and its complementary
endomorphism forces the Jacquet map of that complement to vanish. A second
application of naturality, now with the identity endomorphism, and injectivity of
the adjunction equivalence force the complement itself to vanish.

Algebraic semisimplicity supplies an invariant complement to every invariant
subspace. Projection along that complement is an equivariant idempotent. If the
subspace is nonzero, its projection is nonzero, hence the identity by the first
lemma. Consequently the subspace is the whole carrier. The Jacquet module's
nonvanishing, together with surjectivity of the actual coinvariant quotient,
rules out the zero induced representation.

The unitary specialization uses the published
`Langlands.admissibleUnitarySemisimplicity`. It retains compact-open cofinality,
admissibility and existence of a positive invariant form as hypotheses.
Neither the inducing representation's irreducibility nor finite length of any
representation is assumed.

`unitaryInductionSubrepresentationEquiv` constructs an actual representation
equivalence from any specified nonzero invariant subspace to the whole induced
representation. Its forward map is the actual inclusion, as recorded by its
application lemma.

The proof uses the actual normalized first-adjointness equivalence and its
naturality from `FirstAdjointnessConsequences`, algebraic projections, and the
published admissible unitary complement theorem. That complement theorem uses
compact-open averaging, smooth duality and finite-dimensional Riesz
representation on compact fixed spaces. This proof route does not invoke a
geometric lemma, a cuspidal-support theorem, character independence or Langlands
classification. Broader imported-module dependencies are distinct from these
proof-body dependencies.

This helper does not establish the unitarity, admissibility or irreducible
Jacquet module of a rational rank-one induction. It does not supply any
geometric filtration, opposite-Jacquet duality or analytic criterion, and does
not prove `RationalRankOneSelfAssociationStatement`.
