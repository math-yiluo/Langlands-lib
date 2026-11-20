# Split matching of test functions

`splitMatching` proves `Langlands.BaseChange.SplitMatchingStatement` at an
arbitrary nonarchimedean local field. The result is the split calculation of
Arthur–Clozel (1989), Chapter 1, §5, (5.1)–(5.2), pp. 48–49, and
Henniart–Lemaire (2011), II.2.15, pp. 76–77. The target statement supplies the
Borel structures on \(G=\mathrm{GL}_n(F)\) and \(\mathrm{GL}_n(F^{l+1})\).

`splitProductMeasure` transports the product of \(l+1\) copies of the
given Haar measure on \(G\) through the split group coordinates. The
finite product formula for integrals proves that it integrates split
tensors as required. A Haar measure with these tensor integrals equals the
transported product, by testing the Haar uniqueness scalar on a compact open
subgroup. Every element of \(G\) is a norm, as witnessed in split coordinates
by the tuple with that element in coordinate zero and identity elsewhere.
This proves the off-norm clause of concordance.

For an associated pair \((\delta,\gamma)\) and given associated
centralizer measures, the proof takes coordinate zero of the supplied
norm conjugation to obtain an element \(b\) with
\(b^{-1}(\delta_0\cdots\delta_l)b=\gamma\). The quotient chart sends the
class of \(x\) to the ordinary centralizer coset of \(b^{-1}x_0\) and the
first \(l\) twisted conjugate coordinates \(w\). The centralizer measure
equality and the Weil formulas make its inverse measure preserving for the
product of the ordinary quotient measure and the free product Haar measure.

The product of the twisted conjugate coordinates is the ordinary conjugate
of \(\gamma\) encoded by the first component of the chart. Thus at
\((q,w)\) the descended tensor is its coordinate product evaluated on
`splitProductFiberChart` at \((\mathrm{regularOrbitMap}(\gamma)(q),w)\).
The closed embedding of the regular semisimple orbit makes this joint
function compactly supported and integrable. Fubini on the quotient product
and `integral_splitProductFiber` give the convolution product evaluated
at the ordinary conjugate. The resulting integral is exactly the Library
ordinary orbital integral, for the given compatible quotient measure.
