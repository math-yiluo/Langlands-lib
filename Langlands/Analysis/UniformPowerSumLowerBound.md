# A uniform lower bound among the first power sums

`Langlands.Analysis.UniformPowerSumLowerBoundStatement` gives, for each
positive length `n`, a positive constant `ε` such that every complex tuple
of length `n` and supremum norm at least one has a power sum of norm at
least `ε` among its first `n` positive powers.

If all these power sums vanish, Mathlib's Newton identities show that
every evaluated elementary symmetric polynomial of positive degree
vanishes. Applying its Vieta formula at the negative of one coordinate
then gives that coordinate's `n`th power equal to zero. This holds for
each coordinate, so the tuple is zero. The maximum of the first `n`
power-sum norms is continuous and therefore attains a positive minimum
on the compact unit sphere. Dividing a tuple by its supremum norm puts
it on that sphere. Rescaling back multiplies the `k`th power sum by the
`k`th power of a real number at least one.

This is an internal estimate for the nonnegative Dirichlet series used in
cuspidal pair rigidity. It supplies a coefficient lower bound that depends
only on the dimension when at least one eigenvalue has norm at least one.
