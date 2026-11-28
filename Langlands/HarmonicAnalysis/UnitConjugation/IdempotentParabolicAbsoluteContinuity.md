# Absolute continuity of idempotent parabolic conjugation

Let \(A\) be a finite-dimensional ultrametric normed algebra over a
nontrivially normed field whose closed balls are compact. For an idempotent
\(e\), let \(M\) be its centralizer and \(U=eA(1-e)\) the upper corner.
Let \(C\subseteq A\) be a clopen set of units in additive coordinates.

The map `parabolicChartConjugation` on \(A\times(M\times U)\) is
\((g,Y,Z)\mapsto g(Y+Z)g^{-1}\) on the chart \(g\in C\) and zero elsewhere.
`idempotentParabolicAbsoluteContinuity` proves that the extended map is
continuous and pushes
\((\mu_A|_C)\otimes(\mu_M\otimes\mu_U)\) to a measure absolutely
continuous with respect to any additive Haar measure on \(A\). Here
\(\mu_A,\mu_M,\mu_U\) are additive Haar measures.

## Proof

In finite basis coordinates on \(M\), the constant coefficient of the
characteristic polynomial of \([Y,\cdot]\) on the off-diagonal summand is
a polynomial in \(Y\). Evaluating at \(e\) gives a nonzero value since
`offDiagonalAdjoint_injective` gives zero kernel there. Its nonvanishing
locus is open by continuity. `Langlands.Analysis.ae_eval_ne_zero` gives
nullity of the complement for coordinate product Haar measure.
The basis isomorphism and Haar uniqueness give the same nullity in \(M\).
Fubini gives conullity of the corresponding locus in \(A\times(M\times U)\).

On that locus the constant coefficient criterion gives surjectivity
of the adjoint action. At every point there with \(g\in C\),
`idempotentParabolicSubmersion` supplies a surjective strict derivative.
The extension agrees with the original map on an open neighborhood
of each such point. Applying `submersionMapAbsoluteContinuity` to the
intersection of the conull locus with the chart proves absolute continuity.
The restriction to that intersection equals the restriction to the full
chart because its omitted part is null.

## Source

Harish-Chandra's descent test integral averages over the Levi and upper
corner coordinates and over conjugation by a compact open subgroup.
For the idempotent parabolic this lemma gives the absolute-continuity
part of a direct pushforward argument for the local summability in
Lemma 1.13. See Harish-Chandra, *Admissible invariant distributions on
reductive p-adic groups*, University Lecture Series 16, 1999,
§1.4, pp. 9–10.
