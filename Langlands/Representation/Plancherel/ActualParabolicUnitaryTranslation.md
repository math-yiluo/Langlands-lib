# Unitary restriction of the actual translation

This is an internal restriction of the coefficient constructions for
Waldspurger V.3 formula (1). It connects the full-character generic tensor
in `ActualParabolicTranslation` to the actual unitary coefficient fibers
in `ActualCommonLeviCoherence`. It uses the source and target parabolics
with their corresponding literal Levi anchors and the transported compact
Iwasawa data.

`unitaryParameter_conjugation` applies the published equality for
restriction of characters after forgetting norm-one membership to the
isomorphism of the represented Levi schemes. The induced equality identifies
the full parameter of a transported unitary point with the transport of its
full parameter. `unitaryParameter_conjugation_apply` evaluates it on the
literal Levi: the Levi character of the transported unitary point at `m` is
the Levi character of the original unitary point at `g⁻¹ m g`. It is
obtained by rewriting with `unitaryParameter_conjugation` and then applying
`ActualConjugateLeviTwist.conjugateParameter_apply`.

`pullbackTwistEquiv` is the general same-carrier comparison: for a
topological group isomorphism `e : N ≃ₜ* M`, a smooth representation `B` of
`M` and open-kernel characters `α` of `M` and `β` of `N` with
`β n = α (e n)` for all `n`, the pullback along `e` of the twist of `B` by
`α` and the twist by `β` of the pullback of `B` have the same carrier, and
the identity linear map intertwines them.
`pullbackTwistEquiv_linear_heq` records that its linear equivalence is
`LinearEquiv.refl ℂ B`.

`unitaryTwistEquiv χ g A z` is `pullbackTwistEquiv` for the inverse
literal Levi conjugation `(leviConjugation χ g).symm`, the Levi characters of
`unitaryParameter χ z` and of `unitaryParameter χg (zg z)`, and the
pointwise identity `unitaryParameter_conjugation_apply`. It is the
comparison, with identity linear map, between the conjugate of the twist of
`A` by the unitary point and the twist of the conjugate `Ag` by the
transported unitary point. `unitaryTwistEquiv_linear_heq` states
`HEq (unitaryTwistEquiv χ g A z).toLinearEquiv (LinearEquiv.refl ℂ A)`; it
is proved by unfolding `unitaryTwistEquiv` and applying
`pullbackTwistEquiv_linear_heq`.

`unitaryTranslation χ g A K K' hKK' P hG hK hK' z` is the actual product left
translation `CoefficientConjugation.leviCoefficientLeftTranslation` by `g`
from the coefficient fiber of the source parabolic of `P` to that of its
conjugate `conjugatePresentation χ g K K' hKK' P`, followed by the same-Levi
transport `ActualConjugateLeviTensor.coefficientCongr` along
`unitaryTwistEquiv χ g A z`. The two compactness instances of the left
translation are `ActualCommonLeviTensor.quotientCompact` for the Iwasawa
factorizations of the two parabolics. `unitaryTranslation_eq` states this
composite explicitly and is proved by `rfl`. Neither definition transports
along the equation of parameters `unitaryParameter_conjugation`, so their
values reduce definitionally to the left translation and to the identity
linear map of the inducing carrier. The full unitary parameter group is
used throughout.

`ofCommonLevi` precomposes a displayed target-side common-Levi comparison
by this precise left translation at each unitary parameter. The resulting
maps intertwine the whole external product action on the actual coefficient
fibers. The continuation and regularity of the target-side common-Levi
family are properties to impose through its existing actual-germ
specification when using this adapter for a normalized family.
