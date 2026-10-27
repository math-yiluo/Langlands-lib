# Conditional segment Jacquet multiplicity one

Author: Worker 495.

`Langlands.Classification.SegmentJacquetMultiplicityReductionStatement`
is an internal proposition definition. For an arbitrary p-adic field `F`
and supplied compatible topological data `T`, it states an implication
whose explicit hypothesis is
`GLCuspidalJacquetMultiplicityStatement.{uF,uV,uV}`.
The general count theorem remains a hypothesis.

For every actual supercuspidal representation `A` of positive rank `r`
and positive number of factors `m`, form the increasing and decreasing
normalized segment inductions on `GL_(m*r)(F)`. Each is induced from the
actual uniform product Levi `BlockShape.uniform m r hr`.
Let `σ` and `τ` be the actual external smooth tensors of
`T.segmentFactors A.obj m hr` and `T.segmentFactorsDown A.obj m hr`,
respectively. The conclusion consists of four assertions:

- The upper Jacquet module of the increasing induction has
  `HasJordanHolderMultiplicity` equal to one for `σ.obj`.
- Its opposite Jacquet module has the same multiplicity for `σ.obj`.
- The upper Jacquet module of the decreasing induction has
  that multiplicity for `τ.obj`.
- Its opposite Jacquet module has that multiplicity for `τ.obj`.

All four predicates supply actual composition series and count factors
equivalent to the specified actual tensor. They do not merely specify a
numerical length. The induced objects are exactly `T.segmentInduced` and
`T.segmentInducedDown`, bundled as algebraic representations by `Rep.of`
of their actions. The upper and opposite Jacquet objects are the published
`CuspidalJacquetMultiplicity.upperJacquet` and `.oppositeJacquet`.
In particular, the opposite object uses the actual opposite unipotent
coinvariants with inverse upper full modulus. The inductions retain the
published upper positive half-modulus covariance and right translation.

The field and factor-carrier universes `uF` and `uV` are independent.
The tensor carrier lies in `Type uV`; each induced representation and its
Jacquet quotients have carrier in `Type (max uF uV)`.
The full-count hypothesis is specialized with source and test universes
both equal to `uV`. Positivity of `r` and `m` gives the positive ambient
rank required by that hypothesis.

This is a derived internal interface, with no external source assertion.
Its intended proof instantiates the full-count biconditionals at equal
source and target uniform Levis and at the inducing tensor itself.
Published `segmentFactors_isIrreducible_isLeviCuspidal` and its decreasing
analogue supply irreducibility and cuspidality.
Reflexive Levi association supplies the association hypothesis.
The proved `segmentFactors_tensorStabilizer_count` and its decreasing
analogue identify the two self-association cardinalities with one.
Taking the reverse implication of each biconditional then gives the
four actual multiplicity witnesses. A separate proof module must implement
this argument after the statement is published.

This statement proves no general Jacquet count, adjunction, functor
exactness, detector positivity, map between inductions, strong head,
strong socle or segment constituent existence. Its imports supply the
actual objects and statement interfaces only. No segment, multisegment,
tempered or analytic classification conclusion is used.
