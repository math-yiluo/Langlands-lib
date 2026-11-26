# Descent of the refined numerical counts

`Langlands.Henniart.descentStep` proves
`DescentStepStatement.{uK, uW, uV}`. It descends the refined counts from
`C(M, ψ_{M/L}(x), N)` to `C(L, x, N)` for a cyclic extension `M/L` of prime
degree. The field, Weil carrier, and supercuspidal carrier universes are
independent. The rank bounds on the injection families are those of the
[published statement](HenniartNumericalDescentStatement.md).

For each supercuspidal class over `L` of rank at most `N` and slope at most
`x`, `baseChangeSlope` bounds the slope of every constituent over `M` by
`ψ_{M/L}(x)`. The supercuspidal newvector theorem supplies a finite first
fixed level, so the Swan exponent used by `baseChangeSlope` witnesses
`HasSupercuspidalSwan`. The forward implication of the counting theorem in
`refinedStrata` then puts each constituent used below in the image of the
numerical injection at its own rank.

- **Singleton support.** Weak base change gives a singleton of the original
  rank, and Galois invariance of the support fixes its constituent. Applying
  `ReflectsGaloisInvariance` to its Weil preimage gives an invariant Weil
  class. The [Weil extension argument](HenniartDescentWeil.md) gives `[M : L]`
  distinct extensions with that restriction. Compatibility with the
  singleton decomposition puts all their images in the base-change fibre.
  The same fibre is a surjective image of the norm characters by (W2) and
  (W3a). Their cardinality is at most `[M : L]`, so the distinct images of
  the extensions exhaust the fibre.
- **Orbit support.** If a nontrivial norm character fixes the original class,
  its powers account for every norm character. Then (W3b) supplies a full
  Galois orbit of classes of rank `n / [M : L]`. The Weil preimage of an orbit
  member cannot be invariant: an extension would give singleton base change
  in that smaller rank, and (W1) would fix the orbit member. Coinduction gives
  an irreducible rank-`n` Weil class whose restriction has `[M : L]` summands
  and contains the chosen Weil preimage. By compatibility its image has
  base-change support of that cardinality containing the chosen automorphic
  class. By (W1) the support contains the full Galois orbit, which has no
  repeated entries. The multisets are therefore equal, and uniqueness in
  (W3b) identifies the image with the original class.

The compatibility hypothesis is applied to summands of rank `n` in the
singleton case and rank `n / [M : L]` in the orbit case. With surjectivity in
the stated slope and rank range over `L`, the converse of the counting theorem
in `refinedStrata` uses the supplied Artin conductor existence to recover the
refined count equalities and finiteness over `L`.

## Provenance

The case split is from Guy Henniart, *La conjecture de Langlands locale
numérique pour GL(n)*, §6.8, pp. 520–521 (PDF pp. 25–26), registered as
`henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
The conditional form with refined counts is in the numerical route note
`operator-numerical-llc-route-2026-11-16`, §6.6, Lemma `lem:step`, and §6.5,
Remark `rem:CI2`, in `numerical-LLC-route.tex`, SHA-256
`b57ba9428a0d664d0c6beed75bbc2a2d0d73638718a8080c2f913b75acbbb3c8`.
