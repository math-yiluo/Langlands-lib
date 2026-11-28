# Twisted orbital descent at a regular two-block Levi representative

`TwoBlockTwistedOrbitalDescentStatement` states the two-block instance of
Henniart–Lemaire (2011), II.4.5 (1), printed p. 86, for an exact regular
norm. Let \(F\) be a nonarchimedean local field and \(E/F\) a finite cyclic
field extension with its \(F\)-module topology. Let \(\sigma\) generate
\(\operatorname{Gal}(E/F)\) and have order \(l\).

Let \(B\) have two nonempty blocks, let \(m\) belong to the block Levi
over \(F\), and let \(d\) belong to the block Levi over \(E\). The norm
of each block of \(d\) equals the scalar extension of the corresponding
block of \(m\), and the block diagonal matrix of \(m\) is regular
semisimple. The ambient twisted centralizer of \(d\) is taken to lie in
the Levi.

Use Haar measure on the Levi with its integral points of volume one
(`orbitalDescentLeviHaar`). The embedding of the Levi identifies the
twisted centralizers as topological groups (`twistedLeviCentralizerEquiv`).
The ambient and Levi quotient measures must be compatible with the same
centralizer Haar measure under this identification. For a Schwartz–Bruhat
function \(\phi\), the proposition asserts

\[
O^{G,\sigma}_d(\phi)
 = \mu_G(K)\,|D_{G/M,\sigma}(d)|_F^{-1/2}\,
      O^{M,\sigma}_d(\phi_{P,\sigma}).
\]

Here `normalizedTwistedParabolicConstantTerm` defines \(\phi_{P,\sigma}\)
using \(\delta_P^{1/2}\) and mass-one Haar normalizations on \(K\) and
the integral points of the radical. The source takes \(\mu_G(K)=1\).
The extra \(\mu_G(K)\) records the rescaling of the compatible ambient
quotient measure when the ambient Haar measure is arbitrary. The absolute
value is residue-normalized on \(F\).

## Reduction from a nonelliptic element

`exists_twoBlock_of_sigmaRegular_of_not_sigmaElliptic` chooses an ordinary
regular semisimple associated norm. The norm is nonelliptic, so
`exists_twoBlock_of_regularSemisimple_of_not_regularElliptic` conjugates it
into a proper two-block Levi. `regularLeviNormRepresentative` gives a
twisted conjugate in the corresponding Levi over \(E\), with regular exact
block norms. The block norms combine by `cyclicNorm_leviEmbedding_eq_of_blockwise`.
`sigmaCentralizer_le_leviSubgroup_of_regularNorm` then places the ambient
twisted centralizer inside the Levi. The two-block choice retains regularity
of each norm and allows a block norm to be nonelliptic.

`exists_levi_twistedOrbitalIntegral_of_not_sigmaElliptic` takes
`TwoBlockTwistedOrbitalDescentStatement` as a premise. It transports the
centralizer and quotient measures to the representative through the maps
in `TwistedOrbitalConjugation`. Compatibility and the orbital integral
are preserved. On the Levi the centralizer is closed, so
`compatibleMeasureExists` gives a quotient measure for the transported
centralizer Haar and `orbitalDescentLeviHaar`. Applying the pointwise
identity now gives the formula for the original orbital integral.
`twistedRelativeParabolicDiscriminant_ne_zero_of_cyclicNorm` makes
`twistedOrbitalDescentFactor` strictly positive, and the nonempty compact
open subgroup \(K\) has positive finite Haar measure. Thus the multiplier
\(\mu_G(K)\,|D_{G/M,\sigma}(d)|_F^{-1/2}\) is strictly positive.

The representative and the conditional reduction implement the geometric
step used in Henniart–Lemaire, *Changement de base et induction automorphe
pour GLₙ en caractéristique non nulle*, 2011, II.2.2–2.3, II.4.5 (1) and
II.5.14, Proposition 2 (2), printed pp. 62–64, 86 and 116.
