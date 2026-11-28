# Compact trace witnesses from smoothed descent

Let \(G\) be a locally compact, totally disconnected Hausdorff topological
group with Borel Haar measure, and \(K\) a compact open subgroup with the
restricted measure. Let \(M\) be a compact second-countable Hausdorff topological
group with Borel Haar measure and a continuous homomorphism \(i:M\to G\).
Suppose \(P\) is a test pushforward for \((k,m)\mapsto kyi(m)k^{-1}\).
Take finite-dimensional smooth complex representations \(\sigma\) of \(M\)
and \(\tau\) of \(K\). Let \(f\) be the constant test on \(K\) tensored with
the trace of \(\sigma\), and \(g\) the trace of \(\tau\) extended by zero to \(G\).

If a conjugation-invariant distribution \(D\) is nonzero on \((Pf)*g\), then
`compactTraceDescentWitness` gives an \(m\in M\) for which \(D\) is nonzero
on the left translate of \(g\) by \(yi(m)\). It also gives a nonzero
intertwiner from \(\tau\circ i\) to \(\sigma\) on the subgroup \(i^{-1}(K)\).

The compact trace extended by zero is invariant under \(K\)-conjugation.
The translated-test evaluation inherits this invariance from \(D\). Thus
the smoothed pushforward evaluation becomes the pairing on the slice group,
times the volume of \(K\). The compact trace pairing on the slice group
gives the two witnesses. The theorem `compactTraceDescentWitness_of_finiteSmoothing`
also treats a supplied finite linear combination of compact trace tests whose
convolution fixes \(Pf\). A nonzero \(D(Pf)\) then selects one compact type
by linearity.

This formalizes the witness step in Clozel, *Characters of nonconnected,
reductive p-adic groups*, §3.4, Lemma 5, p. 154.
