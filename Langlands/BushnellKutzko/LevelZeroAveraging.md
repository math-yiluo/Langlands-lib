# Compact averages through a finite quotient

In `averageMap_eq_mean_of_hom`, let `H` be a compact open subgroup, `θ` a
homomorphism from `H` onto a finite group `Q` with a section `t`, and `w` a
vector in a smooth complex representation fixed by the kernel of `θ`. The
normalized average `Compact.averageMap` of `w` is `|Q|⁻¹ ∑_q ρ(t q) w`.

The mean is `H`-fixed because `h · t q` and `t (θ h * q)` differ on the right
by a kernel element, and left multiplication by `θ h` reindexes `Q`. The
compact average fixes this mean and absorbs translation of `w` by every
`t q`, so the mean equals the compact average of `w`. This lemma computes
compression by an adjacent transposition from its finite root quotient.
[Transposition step](LevelZeroSwapStep.md)
