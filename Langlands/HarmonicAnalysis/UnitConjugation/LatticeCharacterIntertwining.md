# Intertwining from lattice character expansions

Let \(L\) be a compact open additive subgroup for a self-dual bicharacter \(e\). Suppose a
homeomorphism \(E\) from \(L\) to a compact group \(K\) transports restricted additive Haar
measure to group Haar measure and sends negatives to inverses. Let the characters of two
finite-dimensional smooth representations expand in these coordinates as finite sums
\(\sum_i e(x,a_i)\) and \(\sum_j e(x,b_j)\). The theorem `latticeCharacterIntertwining` gives a
nonzero intertwining map from the second representation to the first exactly when
some \(a_i-b_j\) belongs to the annihilator of \(L\).

The compact Haar character pairing detects intertwining. Pulling its integral back along
\(E\) converts the inverse-argument character into the complex conjugate of the second
sum. Additive character orthogonality on \(L\) then detects the matching pair of
frequencies.

The theorem `projectedLatticeCharacterIntertwining` treats an ambient lattice \(L\) and
a slice lattice \(M\). For continuous additive maps \(i\) from the slice to the ambient
space and \(p\) back, adjoint with respect to the two bicharacters, use the preceding
criterion on \(i^{-1}(L)\cap M\). The ambient terms restrict to frequencies \(p(a_i)\)
on the slice. Its annihilator is \(p(L^*)+M^*\), so the frequency condition becomes
\(p(a_i)-b_j\in p(L^*)+M^*\).

This is the character-pairing step of Clozel, *Characters of nonconnected, reductive
p-adic groups*, §3.6, Lemma 9, p. 158, under the stated hypotheses on the coordinates
and expansions.
