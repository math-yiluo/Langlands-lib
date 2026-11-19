# Cartan–Iwasawa weight comparison by subgroup indices

The theorem
`Langlands.HarishChandraSchwartz.rationalCartanIwasawaWeightComparisonOfBasis`
proves `RationalCartanIwasawaWeightComparisonOfBasisStatement` at arbitrary
universe `u`.

For a compact open subgroup \(K\) of a locally compact group and a closed
subgroup \(U\) normalized by \(p\), normalize left Haar measure on \(U\) to
give \(Y=K\cap U\) measure one. Its conjugate \(B=pYp^{-1}\) has measure
\(\delta_U(p)\). The formula for the measure of \(Y\) as a union of cosets of
\(W=Y\cap B\) gives \(1=[Y:W]\mu(W)\le [Y:W]\delta_U(p)\). The natural
inclusion of cosets bounds \([Y:W]\) by \([K:K\cap pKp^{-1}]\).
Taking \(U\) to be the actual minimal standard radical and \(p\) the
Iwasawa factor of \(g\) gives a lower bound for the double-coset index
of \(g\) by \(\delta_0(p)^{-1}\), since \(g=pk\) with \(k\in K\).

For the upper bound, set \(L=K\cap K_0\) and normalize ambient left Haar
measure to give \(L\) measure one. The \(K\) double-coset index of \(g\) is at
most \([K:L]\) times the measure of \(LgL\). For \(g\) in the Cartan cell of
\(w=i(y(\varpi))\), this double coset lies in that cell. The published
finite-translate estimate bounds the cell's measure by \(N_c\) times that
of \(K_0wK_0\). The published standard-basis estimate from Waldspurger
I.1 (5) bounds the latter measure by \(C_v\delta_0(w)^{-1}\) uniformly
over dominant \(y\).

Combining the bounds and using positivity of both moduli gives
\(\delta_0(w)\le A\delta_0(p)\), where \(A=[K:L]N_c C_v+1>0\).
Taking square roots yields the comparison with constant \(\sqrt A\).
The factorization \(w=w\cdot 1\) identifies its Iwasawa weight using the
triviality of \(\delta_0\) on \(P_0(F)\cap K\).

The comparison is the one used in Waldspurger's Lemmas II.3.2 and
II.4.4. The implemented proof uses his double-coset volume estimate
I.1 (5) and a subgroup index bound.
