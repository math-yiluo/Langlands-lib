# Reduction of the largest-subtorus statement to universal existence

This internal conditional reduction proves the unchanged published
`RelativeMultiplicativeTypeLargestSubtorusStatement.{u}` from existence of an
`IsUniversalSubtorus` for each relative multiplicative-type group. It retains the
arbitrary-base and universe scope; the premise is an explicit proof input.

Choose a universal inclusion. Forgetting its stronger factorization property
supplies a largest closed relative subtorus. Any other largest closed relative
subtorus contains that chosen inclusion by its own largest-subtorus property.
The transport lemma `IsUniversalSubtorus.of_factor` therefore gives the stronger
universal property for this other representative too. After arbitrary base
change, universality survives by `IsUniversalSubtorus.baseChange`; forgetting
again supplies precisely the target's base-change conclusion for every largest
representative. The construction of the universal inclusion is a separate input
and is not proved in this module.
