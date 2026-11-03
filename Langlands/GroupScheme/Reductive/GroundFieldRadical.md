# Ground-field radical triviality from preservation of unipotence

Author: Worker 1473. Worker 1359 contributed the reduction route.

This internal reduction constructs the embedding
`connectedReductiveToPseudoReductive` from the collection of actual
connected reductive group schemes into that of pseudo-reductive group
schemes over a fixed field. It acts as the identity on underlying group
schemes. The construction is conditional on
`hU : UnipotentFieldExtensionStatement.{u}`. The latter is a separate
structural proof obligation. This module does not prove that statement
or supply an unconditional reductive-to-pseudo-reductive theorem.

First, `SubgroupFunctor.eq_bot_of_baseChange_eq_bot` proves that any
subgroup functor whose base change along a quasi-compact flat surjection
is trivial was already trivial. For an original member, restrict to the
pullback of its test scheme. The base-change point equivalence identifies
the restricted member with an identity point. The projection is an
effective epimorphism, so cancellation proves that the original point is
also the identity. The functor itself need not be represented.

To prove ground-field radical triviality, take any smooth connected normal
unipotent closed subgroup `i : H ⟶ G`. Closedness and the affineness of `G`
make `H` affine, and its smoothness makes it locally of finite type.
Base change to the chosen algebraic closure preserves closedness,
smoothness and normality by the existing subgroup base-change laws.
The published geometric-connectedness theorem preserves connectedness.
The explicit input `hU` supplies unipotence of this base change, with
respect to every representation over the algebraic closure.

The geometric radical-triviality field of `IsConnectedReductive G` now
forces the base-changed subgroup's all-test image to be trivial.
The range base-change theorem and the preceding fpqc reflection lemma
make the original image trivial. The embedding assembles this result with
the original smoothness, affineness and connectedness to provide the
required ground-field `IsPseudoReductive` structure. Injectivity follows
because the underlying group scheme is unchanged.
This is a derived construction on the Library's actual group schemes and
all relative scheme tests. It adds no field restriction.
