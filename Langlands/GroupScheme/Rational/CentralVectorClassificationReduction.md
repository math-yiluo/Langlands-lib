# Central vector subgroups from explicit classification inputs

This derived unit constructs actual central vector-subgroup data from three
explicit proposition premises: `CommutativeVectorClassificationStatement`,
`SplitTorusVectorLinearizationStatement`, and
`UnipotentClosedSubgroupStatement`. It then proves the exact existing
`CentralStableVectorSubgroupStatement`, conditional on those premises.
Every declaration retains arbitrary universe `u`.

`CentralStableVectorSubgroupData b` stores an actual commutative group scheme,
its closed inclusion in the original group, its restricted actual action,
natural linear coordinates and their positive finite dimension. Its proof
fields retain smoothness, affineness, geometric connectedness, connectedness,
unipotence, centrality, stability, nontrivial actual range, smooth relative
dimension equal to the coordinate dimension, and inclusion equivariance on
every scheme test. The data structure itself is defined over any field and for
any acting group; existence has the hypotheses described below.

Every existence construction assumes that the ambient group `G` over the
algebraically closed field `k` is smooth, connected, affine, and unipotent,
and that `SubgroupFunctor.range (𝟙 G) ≠ ⊥`. This last hypothesis is
nontriviality of the actual group functor on all scheme tests. The
characteristic-zero branch permits any affine acting group; the
prime-characteristic and combined constructions use an actual split torus.
The structural proposition premises remain explicit throughout.

In characteristic zero over an algebraically closed field, the existing
smooth-centre construction supplies a nontrivial smooth connected affine
central closed subgroup stable under any given affine acting group. Monicity
of the closed inclusion lets `IsCentral.commGroupScheme` retain the subgroup's
actual group law while recording commutativity. The supplied closed-subgroup
unipotence proposition gives its unipotence. The supplied characteristic-zero
classification then gives natural finite vector coordinates.
`isLinearVectorCoordinates_of_charZero` proves linearity of the actual action
in these coordinates. This branch needs no torus assumption or
torus-linearization premise.

In prime characteristic over an algebraically closed field, the existing
torsion-centre construction supplies an actual nontrivial smooth connected
commutative affine central closed subgroup killed by the characteristic prime
on every scheme test, together with stability and the restricted action.
The supplied p-torsion classification makes it a vector group. The supplied
torus-linearization proposition chooses natural linear coordinates for its
actual split-torus action, retaining zero and multiple weights. Closed-subgroup
unipotence gives the remaining subgroup property. This argument uses the
all-test exponent law directly; it does not replace it with a rational-point
condition.

In both branches, `IsVectorGroupOfDimension.pos_of_range_ne_bot_overRing` proves
positivity from the retained nontrivial image, and
`IsVectorGroupOfDimension.smoothOfRelativeDimension_overRing` identifies coordinate and
smooth relative dimensions. `CharP.exists'` splits an arbitrary field into the
two characteristic cases. `centralStableVectorSubgroupOfClassification`
chooses the resulting actual data from its proved nonemptiness.
`centralStableVectorSubgroup_of_classification` projects those data into every
literal conjunct of the existing central-vector target.

The provenance is the explicit assembly above from the named constructions
and statements. Classification in either characteristic, general split-torus
linearization, and closed-subgroup unipotence remain premises. This unit
proves none of those premises, supplies no unconditional central-vector
theorem, and does not prove the exact semigroup ordered-product theorem.
