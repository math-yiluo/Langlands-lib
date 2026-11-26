# Character functions on open cosets

Let \(i:G\to H\) be an open embedded subgroup and fix \(t\in H\). Both
groups are locally profinite and \(G\) is second countable.
`IsCharacterFunction.twisted_of_openEmbedding` pulls a character function
\(\Theta\) for \(\Pi\) on \(H\) back along \(j(g)=i(g)t\). The result
represents the twisted distribution of the restricted representation
\(\Pi\circ i\) and the endomorphism \(\Pi(t)\).

For each Haar measure on \(G\), the proof rescales a Haar measure on \(H\)
so that its pullback along \(j\) is the given measure. It uses the fact that
right translation transports a left Haar measure to a left Haar measure and
that restriction along an open subgroup preserves the Haar property.
Restricting the rescaled measure to the coset gives the pushforward of the
given measure on \(G\). This transfers local integrability to the coset
coordinates.

The construction `extendAlongOpenEmbedding` transports a test function
to the open coset and extends it by zero to \(H\). The coefficient formula
for the integrated action identifies
the action of the extended function with the integrated action on \(G\)
composed with \(\Pi(t)\). Taking finite-rank traces gives the distribution
identity. The lemma `isAdmissible_of_comp_openEmbedding` supplies the
admissibility comparison: an open stabilizer in the subgroup is open in the
ambient group, and ambient open-subgroup fixed vectors lie in the finite
fixed space for its preimage.

The coset formula is the character comparison in Arthur–Clozel, *Simple
Algebras, Base Change, and the Advanced Theory of the Trace Formula*,
Chapter 1, §2.1, printed p. 11, for the generator component of the cyclic
semidirect product. Source ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
