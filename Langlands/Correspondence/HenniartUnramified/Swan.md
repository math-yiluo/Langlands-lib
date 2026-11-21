# The Swan label of an irreducible Weil class

`Numerical.weilSwanLabel K σ` chooses a natural Artin conductor of the
irreducible class using `weilArtinConductorExistence`, then subtracts the
rank with natural-number truncation. `hasWeilSwan_iff_rank_mul_lastBreak`
proves that the original predicate `HasWeilSwan K σ s` holds exactly when
`s = rank × lastBreak`, as real numbers, on any genuine representative.
In particular `hasWeilSwan_iff_eq_label` shows that the choice of conductor
in the definition does not affect the label.

The proof at a finite inertia presentation uses the published Artin formula:
the codimension at index zero plus the integral of the upper codimension
profile. On positive indices an irreducible representation has fixed space
zero through its last break, and the whole space above it. The actual upper
fixed spaces agree with the finite-presentation fixed spaces. Integrating
these two constant pieces gives rank times the last break. For a positive
break, the index-zero fixed space is zero as well; for a zero break, the
Artin conductor is at most the rank and the truncated subtraction is zero.
This last case includes unramified rank one. Actual equivalences preserve
the break, so the formula applies to every representative of the class.

This normalization is an internal bridge between `HasWeilSwan` and the
one-slope description in the operator's numerical LLC route note. It does
not yet compare the breaks across different base fields.
