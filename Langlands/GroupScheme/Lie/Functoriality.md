# Differentials on actual dual-number kernels

This internal supporting module uses the Library's actual group-scheme points,
dual-number identity kernels, epsilon scaling, adjoint action and weight spaces.
It is needed to compare the roots of an actual standard Levi representative
with the ambient roots.

The module reuses the published `Lie.targetMap` and `Lie.targetMapLinear` from
`Rational.SplitTorusFiniteRank`. Linear injectivity is supplied directly by
`Lie.targetMapLinear_injective`. These are the existing postcomposition maps
on actual dual-number identity kernels, with the same affine hypotheses for
linearity. The kernel group-map injectivity lemma also records the cancellation
argument without an affineness assumption. The new naturality lemmas prove
that these published maps commute with coefficient change and epsilon scaling.

Postcomposition intertwines conjugation by constant points and therefore the
adjoint actions. Applying this identity after every coefficient extension
shows that each weight vector maps to the same character weight. Injectivity
reflects that condition. Consequently a root of a subgroup with monomorphic
inclusion is an ambient root.

No assertion of reductivity, equality of root sets or central-direction
realization is made here. This is a derivation from the published constructions
and uses no additional literature.
