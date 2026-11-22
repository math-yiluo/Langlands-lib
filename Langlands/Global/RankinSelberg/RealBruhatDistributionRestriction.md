# Restriction of real Whittaker distributions to the reversal cell

`Langlands.Global.RankinSelbergGlobal.RealBruhatDistributionRestriction.RealBruhatDistributionRestrictionStatement`
proves that a complex-valued distribution on the open set of invertible
real matrices is determined by its restriction to the reversal Bruhat cell.
The distribution acts on real-valued smooth tests. Its evaluation on each
strictly upper left matrix-unit derivative is zero. On the right, evaluation
on an adjacent matrix-unit derivative multiplies the original value by a
fixed nonzero complex scalar, and evaluation on any other strictly upper
matrix-unit derivative is zero. The statement assumes zero evaluation on
every test whose topological support lies in the reversal cell and concludes
that the distribution is zero.

The reversal cell's product chart has no normal entries and its target is
exactly that cell. The proof uses induction in decreasing inversion count.
In the chart of a lower
cell, each point off the zero section belongs to a cell of strictly
higher inversion count. Such points lie in the higher charts, where the
distribution already vanishes. The transported distribution therefore
vanishes off the zero section and inherits the infinitesimal equations
through the chain rule. `RealBruhatChartVanishing` makes this chart
restriction zero. The chart test transport returns vanishing on the
ambient chart target, and a partition of unity finishes because the
Bruhat charts cover the invertible domain.

This internal support theorem uses infinitesimal covariance as an
explicit hypothesis.
