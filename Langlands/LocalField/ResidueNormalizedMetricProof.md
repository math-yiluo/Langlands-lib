# The topology of the residue-normalized metric

`Langlands.LocalField.residueNormalizedMetric` proves that the distance
\(d(x,y)=|x-y|_F\) defined by the residue-normalized absolute value is
an ultrametric inducing the given topology of every nonarchimedean local
field \(F\). [Statement](ResidueNormalizedMetricStatement.md)

The proof composes the inclusion of the valuation's value group with the
ordered isomorphism `valueGroupWithZeroIsoInt` and the exponential
homomorphism `WithZeroMulInt.toNNReal` at the residue cardinality \(q\).
The exponential sends the adjoined zero to zero and a nonzero value of
multiplicative exponent \(n\) to \(q^n\). Here \(n=-v_F(x)\) for the
value of a nonzero \(x\) in Renard's additive convention. The inequality
\(q>1\) makes the exponential strictly increasing, giving a rank-one
valuation embedding.

`Valued.toNormedField` uses the right uniform structure of the given
additive topological group, so its metric has the given topology by
definition. The distance is the norm of \(x-y\), which applies the
embedding to the restricted valuation of that difference.
`Valuation.embedding_restrict` recovers the original valuation, so the
result is `residueNormalizedAbsoluteValue F (x - y)`. Mathlib's
`IsUltrametricDist` instance for this normed field supplies the strong
triangle inequality.

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, § V.1, printed pp. 103–104 (PDF pp. 109–110),
gives the normalized absolute value and its metric topology. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
