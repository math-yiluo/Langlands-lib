# Full finite-place matching for cyclic base change

`Langlands.BaseChange.FinitePlaceFullMatchingStatement` states both directions
of Arthur–Clozel I.3.1, printed p. 20 (PDF p. 34), over a cyclic field
extension of a characteristic-zero nonarchimedean local field. Here `l` is
the extension degree, `σ` is the cyclic generator, and `n` is the matrix rank.
The two group measures are supplied Haar measures. The compactly supported,
locally constant tests are the Library's `SchwartzBruhat` functions on the
actual matrix groups.

Every upper test has an associated lower test. A lower test has an upper
match if its ordinary orbital integrals vanish at regular semisimple
classes outside the cyclic norm image. In both directions `AreConcordant`
requires equality of orbital integrals at norm-associated pairs with regular
semisimple base element. It uses the ordinary and twisted centralizers, their
associated Haar measures and compatible quotient measures from
`Langlands.BaseChange.OrbitalIntegral`. The existence of those measures
has the separate target `OrbitalMeasureExistenceStatement`.

The compact supports may meet the singular locus. The previously published
`RegularTransferStatement` supplies the regular-support subproblem used by
this route. Fully split finite places use `SplitMatchingStatement` for tensor
tests and cyclic convolution, and the unramified spherical comparison has
its own homomorphism and fundamental lemma targets.

Source: James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and
the Advanced Theory of the Trace Formula* (1989), I.3.1 and its proof in I.3,
registered as `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
