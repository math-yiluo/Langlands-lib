# The literal heterogeneous pair

Author: Worker 645.

`PadicField.heterogeneousPair` is a name for the exact two-block construction in
`ThreeBlockInductionAssociativityStatement`. It first conjugates the action on
`V0` by `ULift.moduleEquiv.symm` onto `ULift.{uV1} V0` and the action on `V1`
onto `ULift.{uV0} V1`, then applies `canonicalNormalizedProductInduced` to the
literal `Shahidi.twoBlocks` shape and `Shahidi.pairFamily`. There is no twist
beyond the canonical positive half modulus. The carrier universe is
`max uF uV0 uV1`, with field and factor universes independent.

`heterogeneousPairToPairEquiv` takes actual factor equivalences from the two
original actions to actions on two carriers in a common universe. It gives an
actual complex-linear equivalence from the literal heterogeneous induction to
the normalized pair on those common carriers. For each factor, it composes
`down` from the exact lifted action with the supplied factor equivalence.
`normalizedPairInducedEquiv` then applies their tensor map to the values of the
actual smooth covariant functions. The inverse applies the inverse factor maps
followed by `up` to their values. It changes neither the group nor its standard
upper parabolic. It requires no smoothness premise for these equivalences.

`isSmooth_heterogeneousPair` is the published smoothness of the actual induced
function representation, applied to this construction. Its conclusion does not
assert smoothness of either original factor.

These definitions and laws have internal derived provenance from
`Induction.HeterogeneousPairs`, `Induction.BlockEquivalence`, and the canonical
normalized induction definitions. They introduce no external mathematical
claim. Applying the pair comparison twice on each side will preserve all four
induction nodes and all eight literal ULift conjugations of the target; the
rank transport and regrouping proof remain separate obligations.
