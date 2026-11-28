# Orthogonality on relative Levi slices

Delorme's normalized pairing (3.7) is defined on the full split component of
the Levi. The packet pairing in Lemma 7.11 tests the relative parameter space
\(i(\mathfrak a_P^G)^*\). This module transfers absolute convergence and
vanishing from positive split-component points with logarithm in the
relative coroot span to all positive split-component points. The argument
uses the given compact subgroup and the same slice measure throughout.

`positiveSplitComponent_factor_coroot` writes a positive split-component point
\(x\) as \(ay\) in the positive split component. To construct \(a\), send \(x\)
to the minimal split torus using the compatible split-component map and write
its logarithm as a real cocharacter \(v\). The projection `toCorootSpan` splits
\(v\) into a coroot part \(d\) and a central part \(v-d\). The split-central
cocharacter range theorem lifts \(v-d\) to the ambient split centre. The
positive torus logarithm realizes that lift by an actual point, which factors
through the Levi split component and gives \(a\). The logarithm of
\(y=a^{-1}x\) is the split projection of \(d\), so
`splitDual_eq_sum_relativeCoroot` writes it as a sum of the relative simple
coroots. The image of \(a\) in the ambient group lies in its positive split
centre, and the parabolic half-modulus of \(a\) is one.

`IsWeakConstantTerm.rightTranslate_eq_smul` passes a scalar right-translation
law from an automorphic form to its weak constant term. The constant term
commutes with right translation. Translating the components of the exponent
expansion preserves their exponents, and scalar multiplication preserves them
as well. Directness of the exponent expansion therefore gives equal sums after
filtering for zero real part.

`weakConstantTermRelativeSliceReduction` applies this law to the unitary
character of the positive split centre, using centrality to turn left
translation into right translation. Split-component equivariance of the
inducing form and the half-modulus calculation give equality of its values
at \(aymk\) and \(ymk\). Thus the full slice integrand is the relative slice
integrand multiplied by the conjugate of the central character at \(a\).
Integrability and a zero integral pass through this constant factor on
\(K\times M(F)\backslash M(\mathbb A)^1\). The factorization and transport
include the case of an empty relative root set.

The argument is derived from the split and relative spaces in
P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics
426 (2023), 109107, §2.1, printed pp. 5–7, the weak exponent sum in
Definition 3.7, p. 13, the defining pairing (3.7), p. 15, and the
relative packet pairing in Lemma 7.11, p. 35.
