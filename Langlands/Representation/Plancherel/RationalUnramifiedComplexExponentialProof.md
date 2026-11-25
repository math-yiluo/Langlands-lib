# The unramified complex exponential is a local biholomorphism

`Langlands.Plancherel.rationalUnramifiedComplexExponential` proves
`Langlands.Plancherel.RationalUnramifiedComplexExponentialStatement.{u}`. The theorem uses any
integer basis \(b\) of the valuation image \(\Lambda(G)\), with the complex-analytic structure
on \(X(G)\) given by the published chart of \(b\).

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July
2026 (registered as `renard-2026-representations-groupes-reductifs-padiques`), V.3.20, printed
pp. 115–116 (PDF pp. 121–122), constructs the exponential from the complex dual of
\(\Lambda(M)\) to \(X(M)\) using \(s \mapsto q^{-s}\). The local biholomorphism in the
[published statement](RationalUnramifiedComplexTorusStatement.md) is the analytic assertion
about that map in the basis chart, with \(G\) in place of the Levi \(M\).

## Lean proof

For each basis element \(b_i\), surjectivity of `rationalValuationImageProjection` gives a
rational point \(g_i\) with valuation image \(b_i\). The basis coordinate of the exponential is
its value at \(g_i\). The canonical evaluation formula and `Module.Basis.constr_basis` give
the coordinate map \(s \mapsto (\exp(c s_i))_i\), where \(c = -\log q\) and \(q\) is the
residue cardinality. The inequality \(q > 1\) gives \(c \ne 0\).

The coordinate map is complex analytic because it is a finite tuple of analytic functions.
Its derivative at \(s\) is the product of the scalar multiplication maps with coefficients
\(\exp(c s_i)c\). Each coefficient gives a complex unit since the exponential never vanishes
and \(c \ne 0\). Lean packages the derivative as a continuous linear equivalence using
`ContinuousLinearEquiv.piCongrRight`.

`ContDiffAt.toOpenPartialHomeomorph` supplies a local homeomorphism at each \(s\).
`OpenPartialHomeomorph.contDiffAt_symm` gives analyticity at every point of its target by
applying the derivative calculation at the corresponding preimage. The result is a
`PartialDiffeomorph` of order `ω`. The published open embedding that defines the basis chart
also gives a partial diffeomorphism by the singleton-chart smoothness lemmas. The coordinate
formula puts the image point in the range of that chart. Composing with the inverse chart
gives the required local analytic diffeomorphism on \(X(G)\).
