# Functional detection from an actual compact-model equivalence

This internal construction for unequal-rank assembly proves that a representation
on a nonzero carrier has a standard mirabolic Whittaker functional whenever
it is equivalent to the actual compact induced model.

The existing `Whittaker.mirabolicCompactEvalFunctional` constructs a functional by sending a vector to
evaluation at the identity of its image under the equivalence.
`mirabolicCompactEvalFunctional_apply` records that evaluation formula.
Intertwining, right translation and the published
left-unipotent covariance give precisely the `mirabolicCharacter`
equivariance law. `Whittaker.mirabolicCompactEvalFunctional_ne_zero` proves that this
functional is nonzero when the source carrier is nonzero: if it were zero,
translating the input
would show that the image of every vector vanishes at every group
element. The image functions are therefore zero. Injectivity of the
equivalence would make the source carrier zero, contradicting the
explicit `Nontrivial` hypothesis.
`Whittaker.hasFunctional_of_mirabolicCompactEquiv` packages the constructed nonzero
functional as the existing `HasFunctional` proposition.

This is an internal algebraic bridge based on the actual evaluations and
translation laws of `Whittaker.MirabolicModels`. Its proof is the
mirabolic-carrier version of evaluation and recovery in the public
`Whittaker.FunctionalExistence` module. It reuses the evaluation constructor
from `Whittaker.MirabolicFunctionalMultiplicityProof`; its nonvanishing
argument does not use the multiplicity theorem. It does not prove existence of an
equivalence, nontriviality of compact induction without that equivalence,
functional multiplicity one, or either source pairing statement.
Irreducibility in the intended application supplies the nonzero source
carrier. The construction itself allows any commutative topological ring
`F` and preserves independent ring and representation
universes. No topology on the representation carrier is used.
