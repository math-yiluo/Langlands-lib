# Jacquet descent of the actual convergent weak-expansion factor

The factor `cFactor` of Waldspurger V.1.1, printed p. 289, descends through
the normalized Jacquet module of the outer parabolic on its original
convergence domain. The outer cocharacter is the one used in `cFactor`,
so the same construction applies in the ordinary and opposite orientations.
The descent uses the actual standard integral with the common compact
normalization and the existing induction-in-stages map.

`cFactorStagedIntertwiner` composes the intertwiners before evaluation.
In order they are the normalizer translation,
the source normalization change, the convergent standard intertwiner,
the inverse target normalization change and the stages isomorphism.
`FirstAdjointness.forward` is the equivariant normalized descent of its
identity evaluation. The formula on an original Jacquet class then agrees
with `factorRestriction` followed by the change to the lower inducing
representation used in `cFactor`.
