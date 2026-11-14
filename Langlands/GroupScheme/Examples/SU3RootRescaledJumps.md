# Positive rescaling of coordinate valuations and jumps

Worker 244. This internal unit proves that changing a coordinate valuation by
a positive real factor preserves existence of an indivisible central jump.
It uses the literal coordinate jump sets of `SU3RootQuotientJumps` and the
condition of `SU3RootJumpParity`; no original-source classification is invoked.

`scaleTop a` multiplies each finite extended real value by `a` and fixes
infinity. It is additive for every real `a` and strictly increasing when
`a > 0`. Composing an additive valuation `ω` with this map gives
`rescaleValuation ω a ha`.

Halving commutes with scaling, so both ordinary coordinate depth and central
depth scale by `a`. Strict and closed depth balls at threshold `a*r` for the
rescaled valuation are exactly the corresponding balls at threshold `r` for
the original valuation. The central subgroup and its multiplication are
unchanged. Consequently both jump sets scale by `a`.

The final equivalence transports a central jump and absence of its quotient
half-jump in either direction. Its reverse normalization uses the threshold
`r/a`, which is legitimate because `a > 0`. The statements apply to any field
in any universe, any ring involution and any additive valuation into
`WithTop ℝ`; neither quadraticity nor conjugation invariance is needed here.
