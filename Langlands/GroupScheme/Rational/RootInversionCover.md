# Fpqc inversion points for actual opposite root subgroups

This internal module constructs the local torus point used in the
nonmultipliable-root argument. A common fpqc inversion point means a
point of the actual torus over a quasi-compact, flat, surjective cover of
the original base that inverts both actual opposite root subgroups on
that test scheme. The definition asserts no rational inversion point.

`exists_fpqc_character_neg_one` uses the published unconditional
`characterFpqc` theorem for a nonzero character of a split torus. It
forms the scheme pullback of that character along the base point of
`Gm` corresponding to the unit `-1`. The first projection is fpqc by
base change, and the second is the required torus point. Naturality of
`Gm.pointsEquiv` proves its character value. The negative character
also has value `-1` because its value is the inverse unit; this argument
works in every characteristic.

`hasFpqcInversionPoint_of_noHigherRoots` applies the published conditional
cyclic-filtration inversion criterion to this same torus point for each
of the opposite characters. It retains semigroup realization, cyclic
root comparison, cyclic weight filtration, smoothness, splitness, a
nonzero character and absence of every positive multiple of degree at
least two on both sides as explicit hypotheses. It does not deduce those
structural statements or the absence condition from nonmultipliability.

This is a deduction from the current Library interfaces. Its geometric
motivation is the inversion point chosen over an algebraic closure in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition C.2.24(iii), printed pp.621–622 (PDF pp.647–648), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The fpqc construction replaces
that choice by an actual cover over the original field. The full exact
rank-one factorization theorem remains outstanding.
