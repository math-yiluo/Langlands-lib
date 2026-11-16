# Universal subtorus

Worker 584. This internal predicate packages the property used to construct the
largest subtorus over an arbitrary base. It is derived for the proof of
`RelativeMultiplicativeTypeLargestSubtorusStatement`, whose notion of largest
subtorus only quantifies over closed relative subtorus inclusions.

`IsUniversalSubtorus j` requires that `j : T → H` is a closed subgroup inclusion,
that `T` is a relative torus, and that, after every base change, every group
homomorphism from any relative torus into the base change of `H` factors through
the base change of `j`. The competing homomorphism has no immersion assumption.
This stronger universal property makes local representatives agree on overlaps.
