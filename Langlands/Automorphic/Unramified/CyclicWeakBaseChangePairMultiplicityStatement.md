# Pair multiplicities under cyclic weak base change

In the module `Langlands.Automorphic.Unramified.CyclicWeakBaseChangePairMultiplicityStatement`,
`CyclicWeakBaseChangePairMultiplicityStatement.{uF,uE,uV,uW}` and
`CyclicWeakBaseChangePairMultiplicityTCStatement.{uF,uE,uV,uW}` state the
same fixed-extension property `CyclicWeakBaseChangePairMultiplicityOver`.
The companion requires the base field `F` to be totally complex.

Let `E/F` be a cyclic Galois extension of degree `d`, and let `η` have
kernel exactly the idele-class norm image. Supply two unitary isobaric
data over `F` and a unitary weak base change of each over `E`. The number
of equal pairs of cuspidal constituents of the two data over `E` equals
the sum, for `0 ≤ i < d`, of the corresponding pair counts over `F`
with the first datum twisted by `η^i`. A pair count uses the actual
full cuspidal class and counts each occurrence in each multiset. Each
twist uses the existing finite-order determinant twist of an actual
cuspidal class. The proof of finite order inside the statement uses
triviality on the norm of each power of `η`.

This is the order-at-one consequence of Arthur and Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), Chapter III, Lemma 4.3, printed p. 204. The calculation
in the proof of III.3.1, p. 201, applies at arbitrary cyclic degree.
Use a contragredient in the second variable and apply (2.1)–(2.3),
pp. 199–200, to the pair of unitary cuspidal constituents at each
index. The statement extends the pair counts additively to all the
constituents of the supplied isobaric data, as in the isobaric products
in the proof of III.4.2, pp. 204–210.

For the proof, choose compatible cofinite sets of finite places for the
supplied weak transfers and all actual spectral presentations. The
presentations of the twists give scaling by `η_v(ϖ_v)`, and the
contragredient presentation gives inverse eigenvalues. At a base place
with residue degree `f`, each quotient of eigenvalues `x` contributes
through the factors `1 - η_v(ϖ_v)^i x X`. The exact local order `f` of
`η_v(ϖ_v)` gives `(1 - x^f X^f)^(d/f)` after multiplication over `i`.
There are `d/f` actual places above the base place, with residue
cardinality `q_v^f`, and the two supplied weak base changes raise the
spectra to the `f`-th power at all of them. Apply the local equality to
the partial Euler products on `Re(s) > 1`. Add the meromorphic orders
at `s = 1`, using the partial unitary cuspidal pair order for actual
constituents and their contragredients. Its simple poles of order one
occur exactly for equal original constituents, and the other pairs
have order zero. This comparison uses weak finite-place transfer. On
the totally complex route the partial-order proof can use the complex
archimedean theory.
