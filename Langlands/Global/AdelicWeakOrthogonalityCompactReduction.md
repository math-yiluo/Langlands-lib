# Reduction of weak constant-term orthogonality to a reference compact

The end of Delorme's proof of Theorem 7.9 uses tests obtained from one
square-integrable inducing form at a time for the fixed reference compact.
`WavePacketWeakConstantTermReferenceCompactStatement` records the weak
constant-term conclusion for that class of tests and one reference compact
for each standard parabolic family.

Conjugate the reference compact at infinity so its infinite projection
agrees with the given compact. First translate a reference packet with one
inducing form, retaining a one-form presentation. Apply the finite compact
packet comparison to that presentation. Orthogonality for the given compact
then implies orthogonality for the inverse translate of the tested form at
the reference compact. The Haar-preserving right translation on the rational
quotient yields the pairing identity, using rational invariance of each
entry to identify its values on quotient representatives.

The weighted form and its weak constant terms transport under the inverse
infinite translate since the given compact and the conjugate reference
compact induce the same archimedean automorphy condition. Apply the reference
orthogonality result. Transfer the pairing back by infinite and then finite
compact change, including absolute convergence at each positive Levi slice.
This uses the finite compact comparison and imaginary-axis continuation of
the cut inducing forms.

The Levi pairing is the one in Delorme, *On the spectral theorem of
Langlands*, Advances in Mathematics 426 (2023) 109107, §3.4, (3.7).
The single-form tests are those used before Lemma 7.11 on pp. 34–35.
The compact comparison extends that choice of tests to the quantification
over maximal Iwasawa compacts in
`WavePacketWeakConstantTermOrthogonalityStatement`.
