# Transporting a certified pair polynomial from a completion

`DistinguishedPairPolynomialTransportStatement.{uF,uD,uV,uW}` compares two
equal-rank actions over a bundled p-adic field `F` with the actual representatives
of two generic classes over a bundled p-adic field `D`. The fields are identified
by a bicontinuous ring equivalence `a`. The two original actions, in independent
carrier universes, are equivalent to the pullbacks of the representatives by the
entrywise map of `a`. The polynomial of the given original pair is certified by
`IsPadicRankLPolynomial`. The other polynomial is certified by
`IsAutomorphicPairLPolynomial` for the given generic classes. Both certificates
use their own additive character and self-dual measure. The two polynomials are
equal.

`distinguishedPairPolynomialTransport` first reads the class polynomial on the
supplied representatives and uses genericity to obtain an actual JPSS
certificate on those representations. Pulling back the character and Haar
measure along the field equivalence gives a JPSS certificate on the two
representation pullbacks. Equivariance transfers it to the original pair.
Any two nontrivial additive characters on the original field differ by scaling
by a field unit. Character-change invariance and uniqueness across additive Haar
measures then compare this transported certificate with the supplied one.

The construction combines the Library's generic `IsLanglandsPairLPolynomial`
comparison, field transport, and character and measure invariance. It supplies
the identification of actual local factors of the globalized representations
with the prescribed local certificates. That identification is the transport
step in Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), Chapter 1, §6.4, the application of Lemma 6.11 on
printed pp. 65–66 (PDF pp. 79–80). The retained source ID is
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The representation identifications and genericity are inputs to this transport.
