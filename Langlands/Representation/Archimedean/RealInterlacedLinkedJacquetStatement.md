# The linked Jacquet functional for two interlaced induction blocks

Lean module: `Langlands.Representation.Archimedean.RealInterlacedLinkedJacquetStatement`.

This module states one statement and proves nothing. It imports
`RealLinkedJacquetPairReduction` (Library) for the conclusion
`RealLinkedJacquetFunctionalExists` and for the statement `RealInducedInducedLinkedJacquetFunctionalStatement`
(II), of which it is a case.

## Notation

* `ComplexCharacterData` `d` is the character `(z/|z|)^m |z|^{2t}` of `ℂ^×`, with weight
  `m = d.weight` and exponent `t = d.exponent ∈ ℂ`. `RealBlock.induced d` is the Library's
  induction block of rank `2`. For `m ≠ 0` its Mœglin datum is `(2, t, D_{|m|})`
  (`realBlockMoeglinData`).
* `RealLinkedJacquetFunctionalExists n ds` (module `RealLinkedJacquetPairReduction`): the
  `O(n)`-finite functions of `realStandardModule n ds` carry a nonzero real Jacquet functional `ℓ`
  with exponents `a`, signs `e`, a position `p` with `p + 1 < n` and `k' : ℕ` such that
  `a_p - a_{p+1} = 1 - k'` and `ℓ(π(1 ⊗ E_{p+1,p})^{k'} v) = 0` for every `v`. This is the
  conclusion of S2 (`RealLinkedJacquetFunctionalStatement`, Library module
  `RealLinkedJacquetFunctional`).

## The statement

`RealInterlacedInducedInducedLinkedJacquetFunctionalStatement` (Interlaced): for all `d e :
ComplexCharacterData` and `k : ℕ` with

* `d.weight ≠ 0` and `e.weight ≠ 0`,
* `0 < k` and `k ≤ min(|d.weight|, |e.weight|)`,
* `d.exponent - e.exponent = ||d.weight| - |e.weight||/2 + k` (an equation in `ℂ`),

`RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e]` holds.

### What the hypotheses mean

Write `p = |d.weight|`, `q = |e.weight|`, `s = d.exponent`, `t = e.exponent`, and
`u_1 = s + p/2`, `v_1 = s - p/2`, `u_2 = t + q/2`, `v_2 = t - q/2` (the position exponents of the
four positions). The exponent equation with `k ≥ 1` is the first disjunct of
`MoeglinDatum.IsLinked (2, s, D_p) (2, t, D_q)`. It forces `Re t ≤ Re s`. So the hypotheses of
Interlaced imply those of II for `[induced d, induced e]`. All four differences below are
integers:

* `u_1 - u_2 = (p - q + |p - q|)/2 + k > 0` and `v_1 - v_2 = (q - p + |p - q|)/2 + k > 0`;
* `u_2 - v_1 = min(p, q) - k`.

So `k ≤ min(p, q)` says `v_2 < v_1 ≤ u_2 < u_1`: the two segments interlace, or touch when
`k = min(p, q)`. The complementary case `k > min(p, q)`, where `v_1 > u_2`, is proved as
`separatedInducedInducedLinkedJacquetFunctional` in the module `RealBlockFlatJacquet`.
There `realInducedInducedLinkedJacquetFunctional_of_interlaced` derives II from Interlaced.

## Provenance and why the statement is expected to be true

The statement is internal. It is the case `ds = [RealBlock.induced d, RealBlock.induced e]`
of S2 for the interlaced pairs. This list has rank `4`. It is Langlands-ordered (`Re t ≤ Re s`),
and its two Mœglin data are linked. So S2 implies Interlaced by specialization.

The justification of S2 is in the Library's `RealLinkedJacquetFunctional.md`, "two discrete
series". In its notation (`s - t > |p - q|/2`), Interlaced is the range
`|p - q|/2 < s - t ≤ (p + q)/2`:

* for `min(p, q)/2 < s - t ≤ (p + q)/2`, its cases (a) and (b) apply. One block is embedded in its
  principal series, the other is moved past it by convergent intertwining operators, and the last
  crossing `(u_1, v_2)` gives the functional with `k' = u_1 - v_2`;
* for `s - t ≤ min(p, q)/2`, its case (c) applies, via a translation functor from case (a)
  (Bernstein–Gelfand 1980, Theorem 4.1 and Remark 4.2(a)).

The Langlands quotient is the image of the Langlands intertwining operator (Knapp 1986,
Theorem 7.24). In Speh's case `p = q`, `s - t = 1`, Sahi and Stein (1990) realise it inside a
module induced from characters of `GL_2 × GL_2` composed with the determinant. This is a
cross-check only. The sources are listed in `RealLinkedJacquetFunctional.md`. No statement is
quoted from them.

## Proof

The statement is proved as `Langlands.Archimedean.realInterlacedInducedInducedLinkedJacquetFunctional`
in the module `RealInterlacedMirror`, the last of the six modules `RealInterlacedJacquet`,
`RealInterlacedColumns`, `RealInterlacedChain`, `RealInterlacedEngine`, `RealInterlacedProof` and
`RealInterlacedMirror`. That proof does not follow the route of S2 sketched above. The
rank-one test-vector method of `RealBlockFlatJacquet` alone proves only the separated case: in
the interlaced case the crossing `(v_1, u_2)` has `v_1 - u_2 ≤ 0`, so it gives no binomial
functional. The proof instead moves the exponents by the Frobenius maps of a chain of explicit
Jacquet functionals: a flat functional (`μ = 1` or `sgn`) at one block, a tail multiplier at the
middle block and a generic multiplier at the other outer block. A dichotomy at the middle block
then gives the functional, and explicit test functions show that it is nonzero.
`RealInterlacedMirror.md` gives the outline.
