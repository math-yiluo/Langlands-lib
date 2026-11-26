# Weak constant term orthogonality along the full standard parabolic

`WavePacketWeakConstantTermTopOrthogonalityReductionStatement` gives the full
standard parabolic case of `WavePacketWeakConstantTermOrthogonalityStatement`
from `WeakConstantTermComponentPairingIntegrableStatement`. The compact can
be any maximal compact satisfying the minimal-parabolic Iwasawa condition.
The conclusion includes convergence and zero at every point of the actual
positive split component.

At the full standard index the parabolic and Levi maps are isomorphisms
onto \(G\). The one coset term in the Eisenstein series is entire in its
parameter. Pullback along the parabolic isomorphism identifies the parameter
with an ambient character and identifies its Iwasawa height evaluation
with ambient character evaluation. The theorem
`StandardParabolicFamily.isWavePacket_top_ambientProfile_mul`
therefore realizes the product of an inducing form and a split-centre
Fourier profile as a wave packet for the original compact.

The full inducing form is invariant under the positive split centre because
the half-modulus is one. Its rational invariance comes from the full Levi
isomorphism. A translated smooth compactly supported coefficient takes
the value one at the unitary character of the tested form. Fourier inversion
and the product decomposition of the full rational quotient then express
the full packet pairing as a nonzero scalar times the norm-one pairing of
the inducing form with the tested form. Complex conjugation puts the
orthogonality hypothesis in this order, so the norm-one integral is zero.

The supplied component integrability and a finite sum give integrability
on each Levi slice. The unitary character also identifies the tested form
with its own full weak constant term by `isWeakConstantTerm_top` and
`IsWeakConstantTerm.unique`. For a fixed compact variable the Levi quotient
is transported to the ambient norm-one quotient by `normOneQuotientIso`
and then translated on the right. The Levi isomorphism rescales the Haar
measure by a positive constant and the right translation preserves the
ambient measure. The split-component translate contributes just the
conjugate unitary character. Each inner integral is thus a constant times
the zero norm-one integral. Fubini gives the result on the compact and
Levi quotient product.

The one-term series is the full-parabolic specialization of Bernstein and
Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, §2.2, (2.1), p. 191.
The registered PDF `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`
has SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
The pairing is from Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, (3.7), p. 15,
and the central Fourier inversion preceding Lemma 7.11, p. 35.
The published PDF in `delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
