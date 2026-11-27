# Last-row descent for real equal-rank integrals

`Langlands.Global.RankinSelbergGlobal.realEqualLastRowDescent` proves
`RealEqualLastRowDescentStatement`. Let \(W\) and \(V\) be continuous functions on
\(\mathrm{GL}_{n+2}(\mathbb R)\) with opposite Whittaker characters and the simple-root
gauge bounds `HasGaugeBound`. Suppose that for every Schwartz test on the last row the
ordinary equal-rank integral of this pair vanishes on a right half-plane. The ordinary
adjacent-rank integral of \(W\) and \(g\mapsto V(\operatorname{diag}(g,1))\) then vanishes
on a right half-plane. Both quotient measures are arbitrary compatible choices.

## Proof

Choose a smooth compactly supported bump equal to one at the last standard row and
multiply it by each Fourier character of the row space. The resulting tests are Schwartz.
Their integrands have the same absolute value, so `RealEqualConvergence.exists_convergence`
for the original bump gives a common convergence half-plane. The exponent of the determinant
enters through an exponential of its logarithm. This gives holomorphy of every modulated
integral on the common half-plane by `differentiableOn_integral_cexp_mul`. The identity theorem
`eq_zero_on_right` transfers each test's vanishing to that half-plane.

`lastRowChart_integral` writes the larger quotient integral in coordinates
\(([g],x,u)\) with representative \(\begin{pmatrix}g&0\\x&u\end{pmatrix}\) and density
\(|\det g|^{-1}\,d[g]\,dx\,d^\times u\), up to a positive constant. At a fixed equal-rank
spectral point \(s\), first integrate against \(|\det g|^{-1}\,d[g]\). Fubini identifies the
integrals for the modulated tests with the Fourier coefficients of the resulting integrable
fiber function in \((x,u)\).

Write the representative as \(\operatorname{diag}(g,1)L(x,u)\), where
\(L(x,u)=\begin{pmatrix}1&0\\x&u\end{pmatrix}\) has identity upper-left block. The fiber is the
adjacent-rank integral of the two functions translated on the right by \(L(x,u)\), with the
second function evaluated on the padded smaller group. Its multiplier is the bump at
\((x,u)\) times \(|u|^s\). The adjacent-rank parameter is \(s-\tfrac12\) because its
determinant exponent must be \(s-1\). The compact-translate gauges and
`ordinary_halfPlaneDomination` give continuity of the smaller integral as \(L\) tends to
one, by dominated convergence. The fiber thus extends continuously at \((0,1)\).
`eq_zero_of_fourier_units_eq_zero` gives zero there. At that row the bump and multiplier
are one and \(L(0,1)=1\), which yields the asserted vanishing.

## Source

H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), equations (2.4) and (2.6),
author-posted p. 6, and the equal-rank case of Lemma 14.1, author-posted pp. 106–107.
Jacquet uses the same lower block integral and determinant density to express the padded
integral through equal-rank Schwartz tests. The Lean proof recovers the identity fiber by
Fourier uniqueness. `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
