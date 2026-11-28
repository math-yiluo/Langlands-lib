# Raising the common rank of a real smooth Whittaker pair

`RealPairedRankTransferStatement` takes two jointly continuous complex
Banach representations of real general linear groups of positive ranks.
The continuous complex-linear form on their completed projective product
uses the genuine word-derivative topology of the two groups acting
independently. It has independent upper-unipotent covariance at opposite
nonzero real scales and common upper-unipotent invariance under
simultaneous leading padding. The quotient measures at every rank are
supplied with their compatibility data. The rank steps use the supplied
additive and nonzero bi-invariant trailing Haar measures.

Choose a starting positive common rank and a strictly larger terminal
common rank that fits in both factors. The smaller quotient integral
without a row test, at determinant exponent `s` minus the rank gap,
times a positive scalar is a finite sum of integrals at the terminal
rank and determinant exponent `s`. The scalar depends only on the
measure comparisons. The finite family is independent of `s`. If an
ambient rank still exceeds the terminal rank, the terminal terms have
no row test. If both ambient ranks equal it, each terminal term has a
compactly supported Schwartz test of the full last row. Absolute
integrability of these terms at a spectral point suffices for the
identity and the corresponding absolute integrability at the
starting rank.

Use the adjacent comparison at the starting rank. At each
intermediate rank, a larger ambient factor absorbs the Schwartz weight
into a genuine smooth vector. If this rank is the terminal rank, use
row absorption when a further ambient column exists and retain the
compact Schwartz row otherwise. The downward induction flattens the
finite families for the next-rank vectors into one finite family and
multiplies the two positive measure scalars. The shift of one at each
step gives the total determinant exponent difference.

This is the iteration in Lemma 14.1, pp. 105–107 of the author-posted
edition, with the supplied Haar measures and the absolute integrability
premise explicit.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=105).

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.

`RealPairedRankTransferBanachStatement` makes the completeness hypotheses on the two representation spaces explicit.
