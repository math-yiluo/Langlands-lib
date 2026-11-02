# Normalized measure on the actual two-block rational quotient

This is a derived transport of the existing `matrixQuotientHaar` through
`GeneralLinearBlockUnipotent.quotientHomeomorph`. The domain is the actual
principal-image left quotient of the two-block subgroup functor, with its
existing quotient topology and its Borel sigma algebra. Both block sizes may
be zero. The original hypothesis `CompactSpace (AdeleQuotient F)` remains
explicit throughout.

`rationalQuotientMeasure` is the pushforward of the original matrix measure by
the inverse homeomorphism. It is a probability measure, so its total mass is
exactly one. Pushing it forward by the forward homeomorphism recovers the
original matrix measure, by the inverse identities of the measurable
equivalence. The two homeomorphism directions are measure preserving for
these exact measures.

Positive right translation preserves this measure. The proof writes actual
quotient translation as the conjugate, by the proved quotient homeomorphism,
of addition of the translating point's reduced matrix coordinates. The
original matrix measure is additive Haar measure, so that addition preserves
it. Composing the three measure-preserving maps proves invariance on the
actual quotient.

These constructions use the existing matrix Haar normalization without
changing any original general-linear definitions. They do not compare this
probability measure with an independently normalized ambient Haar quotient,
or prove general reductive finite volume, additive quotient compactness,
reduction theory, or an integral comparison.
