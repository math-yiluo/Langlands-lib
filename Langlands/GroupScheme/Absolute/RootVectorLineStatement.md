# Actual absolute root subgroups are vector groups of dimension one

`AbsoluteRootVectorLineStatement` is an unproved proposition for the actual
intrinsic root subgroup functors in `Rational.RootSubgroup`. Its universe `u`,
algebraically closed ground field and characteristic are arbitrary. The ambient
group is connected reductive. The given map from a commutative group scheme is
both a split subtorus and a maximal torus of that group.

For each nonzero adjoint root of that map, the conclusion supplies an actual
group scheme `U` and homomorphism `j : U ⟶ G`. The map is a closed subgroup
inclusion. `IsRepresentedBy` identifies its full range with the already defined
intrinsic root functor on every test scheme. The final predicate is precisely
`RelativeRoot.IsVectorGroupOfDimension U 1`: the point group of `U` on each
test scheme is naturally the additive group of one global function. This is
the Yoneda formulation of an isomorphism with the additive group scheme.
It includes nonreduced tests and is stronger than an assertion about rational
points or the dimension of a tangent space.

The source is J. S. Milne, *Algebraic Groups*, corrected reprint (2022),
registered as `milne-2022-algebraic-groups`, Definition 21.10 and Theorem
21.11(b),(c), printed pp.428–429, PDF pp.439–440. The theorem says that the
root group is isomorphic to the additive group. Its proof obtains that
isomorphism from the rank-one homomorphism from `SL₂`, not from reducedness
alone. The author’s registered 2022 errata, snapshot 4 November 2026, was read;
it gives no correction to this passage.

This is a derived formulation of that assertion using the Library's
intrinsic functor. Milne defines the root group by contraction in the
centralizer of the codimension-one subtorus. The Library defines it by an
orbit extension through the actual character, with value equal to the
identity at zero. A proof of the present proposition must identify that
existing functor with the source root group on all tests and supply the
natural additive coordinates. Neither identification nor the additive
coordinates occur as input hypotheses. In particular, the statement does
not replace the full character kernel by a smooth kernel or require the
character to be primitive.

The general-field `RootSubgroupVectorStatement` allows arbitrary vector
dimension and does not supply this conclusion. Reducedness of the root
system also does not determine root multiplicities. The present proposition
isolates the additional geometric result needed by
`Reductive.RootGeneratedCentralizer`: both the ambient root and each root of
the normal semisimple subgroup must be vector groups of dimension one.
This file proves neither the proposition nor the unconditional
`SemisimpleAlmostSimpleGenerationStatement`.
