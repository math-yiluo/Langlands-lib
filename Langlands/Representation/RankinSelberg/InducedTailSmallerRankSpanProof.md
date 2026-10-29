# Smaller-test-rank tail Laurent-span inclusion

Author: Worker 647. The value-continuation transport and canonical assembly
adapt Worker 646's shared equal-tail-rank draft, including
`reindex_appendIdentity_congr`. Worker 53 identified the compatible-measure
uniqueness route.

`Langlands.RankinSelberg.inducedTailSmallerRankSpan.{uF,uV₁,uV₂,uW}`
proves exactly the closed published proposition
[`InducedTailSmallerRankSpanStatement`](InducedTailSpanStatement.md).
The field and the three representation carrier universes remain independent.
The theorem applies `inducedTailSmallerRankSpan_of_extension` to the published
[`Langlands.Whittaker.twoBlockWhittakerExtension`](../Whittaker/TwoBlockExtensionProof.md).
The helper isolates the integral comparison from that extension theorem.

The internal lemmas lie in
`Langlands.RankinSelberg.InducedTailSmallerRank`. The coordinate lemmas compose
the actual `appendIdentity` inclusions after entry-preserving `finCongr`
transport. They verify matrix entries without permuting the two blocks.
`det_reindex_finCongr` removes the arithmetic index transport from the
determinant; the published `det_appendIdentity` then identifies it with the
small matrix's determinant.

With a positive appended identity block, `lastRow_appendIdentity_fixed`
identifies the last row with the last standard basis row, independently of
the input matrix. `exists_schwartzBruhat_one` takes a compact neighborhood of
that point, refines it to a clopen neighborhood contained in the compact set,
and uses its characteristic function. That function is a Schwartz–Bruhat row
test equal to one at the standard row. In the final assembly, the canonical
p-adic field supplies the Hausdorff certificate `fieldT2`; its valuative
topology supplies the nonarchimedean ring instance and hence total
disconnectedness. No separation or disconnectedness hypothesis is added.

For tail gap `k` and additional head size `d`, `halfModulus_weight` proves

```text
|det(g)|^(d/2) * |det(g)|^(s-(k+d+1)/2)
  = |det(g)|^(s-(k+1)/2).
```

The real power is included in the complex numbers. Positivity of the
determinant absolute value justifies its identification with a complex power
and the addition of exponents.

Given an actual restriction identity on all diagonally embedded small
matrices, `integrand_eq` proves pointwise equality of the two zero-row
unequal-rank integrands for every spectral parameter and every quotient
class. `converges` transfers the actual product-measure integrability in both
directions, and `integral_eq` equates the actual iterated scalar integrals.
These lemmas allow any common quotient and zero-row rectangular measures.
They use neither a Dirac simplification nor an existence theorem for
continuations.

`values_subset` retains both literal gap parameters while the two large-rank
equalities transport the representations. It eliminates these equalities
before using the gap equation `l = k+d`. Given the coefficient extension
property, it transfers each actual tail value: the original inverse-character
test coefficient and its membership are retained, `converges` transfers its
right half-plane of convergence, and the published
`RationalContinuationLinear.continuation_of_eq_on_right` transports its given
rational continuation using `integral_eq`.

In the assembly, write `A = a+1`, `B = b+1`, `T = t+1`, with
`T < B`. Both quotient measures live on `N_T \ GL_T` and are compatible with
the same normalized ambient and unipotent Haar measures.
`unipotentQuotientHaar_unique` therefore equates them exactly; the measure
scalar is one. The literal gaps are `b-t-1` and `a+1+b-t-1`, whose difference
is `A`. The extension formula is evaluated at the actual transported
`diag(g,I_(B-T))`. The composed embedding is the full zero-row embedding,
the cutoff evaluates to one on its constant last row, and the determinant
factor is `|det(g)|^(A/2)`. The weight lemma cancels that factor against the
full spectral shift. `values_subset` and `zetaSpan_mono` give the required
Laurent-span inclusion.

All four independent universes are retained, including the literal
ULift-conjugated canonical normalized induction. The closed conclusion
preserves arbitrary Whittaker-type block and test representations, the supplied
self-dual additive Haar measure, its actual zero-row rectangular product
measure, and every independently compatible quotient-measure choice. It
assumes no L-polynomial existence, irreducibility, induced Whittaker type,
extension formula, integral comparison, or span comparison. The last three
are proved by the imported extension theorem and the lemmas in this module.

These are derived consequences of the published matrix definitions,
compatible-measure uniqueness, continuation transport, and basic locally
compact totally disconnected topology. They implement the smaller-test-rank
calculation in JPSS section 9.3, printed 455–457 (especially printed 456).
The extension formula is Proposition 9.1, printed 452–454. The registered
original is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The relevant original scans were read during development. A bounded source
audit found no source-specific erratum in the checked project locations.
The constant-last-row cutoff is an internal simplification for this literal
zero-row embedding: it is one on every row where a tail coefficient can
contribute, without requiring a support theorem for that coefficient.
