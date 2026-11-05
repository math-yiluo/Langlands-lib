# All-characteristic assembly from the prime-exponent domination case

This internal assembly isolates the remaining elementary input for
`UnipotentSplitTorusDominationStatement`. The proposition
`PrimeExponentSplitTorusDominationCase` says that, over every field of
prime characteristic `p`, a smooth connected affine commutative
unipotent group killed by `p` and supplied with pointed split-torus
domination is split unipotent.

`unipotentSplitTorusDomination_of_primeExponent` derives the exact
all-characteristic target from this explicit premise. The implemented
proof uses the published derived-subgroup reduction to reduce to
commutative groups. The field characteristic is either zero or prime.
In characteristic zero the commutative splitness theorem supplies an
actual split series without needing domination. In prime characteristic
the published prime-power-image reduction applies the supplied
elementary case. All series, groups and quotients remain over the
original field, including finite or imperfect fields.

`splitSeriesOfPrimeExponentDomination` chooses the resulting finite
represented additive series. This is a conditional support result;
it does not establish the elementary case or the unconditional target.
It introduces no change to the target's existing predicates. Its
provenance is the composition of the named Library reductions and the
elementary dichotomy for the characteristic of a field.
