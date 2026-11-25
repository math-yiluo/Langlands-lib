# The base case of Henniart's numerical correspondence below the ramification index

This module states one proposition and proves nothing. It is the base case of
Option II in the operator's numerical local Langlands route note. Assume the
GL-side upper bound (I1) and the Laumon–Deligne count (LD). If numerical
injections exist over a p-adic field `K` in all ranks at most `N`, then the
refined counts agree over `K` up to every slope below the absolute
ramification index `e_K`.

## The proposition

`Langlands.Henniart.NumericalBaseCaseStatement.{uK, uW, uV}` is the implication

```
SupercuspidalStratumUpperBoundStatement.{uK, uV} →
  LaumonDeligneCountStatement.{uK, uW} →
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (N : ℕ),
    (∀ k : ℕ, k + 1 ≤ N → ∃ φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
        Numerical.IsNumericalInjection K φ) →
    ∀ x : ℝ, x < K.canonicalTopologicalData.ramificationIndex →
      Numerical.CountsAgreeUpToSlope.{uK, uW, uV} K x N
```

In words: assume (I1) and (LD). Let `p` be a prime, `K` a p-adic field and
`N` a natural number. Suppose that for every rank `n = k + 1 ≤ N` there is a
numerical injection from the irreducible `n`-dimensional Weil classes of `K`
to the supercuspidal classes of `GL_n(K)`. Then `C(K, x, N)` holds for every
real number `x < e_K`.

The ingredients are published Library declarations.

- `SupercuspidalStratumUpperBoundStatement` is (I1): for every prime `p`, every
  `K : PadicField.{uK} p` and all `k s f`, the extended cardinality of
  `S_K(k + 1, s, f)` is at most the polar-part count `ν(k + 1, f, s; q_K)`
  ([statement](HenniartGLUpperBoundStatement.md)).
- `LaumonDeligneCountStatement` is (LD): for every prime `p`, every
  `K : PadicField.{uK} p`, every `k` and `1 ≤ s < (k + 1) e_K`, we have
  `T_K(k + 1, s) = T_K(k + 1 + s, s)`
  ([statement](HenniartLaumonDeligneStatement.md)).
- `Numerical.IsNumericalInjection K φ` says three things. First, `φ` is
  injective. Second, whenever `σ` has natural Artin conductor `a`, the
  conductor of `φ σ` is `a`. Third, `φ` commutes with unramified twists
  ([numerical statement](HenniartNumericalStatement.md)).
- `Numerical.CountsAgreeUpToSlope K x N` is `C(K, x, N)`. For all `k s f` with
  `k + 1 ≤ N` and `(s : ℝ) ≤ (k + 1) x`, it requires that
  `W_K(k + 1, s, f)` and `S_K(k + 1, s, f)` have equal extended cardinality in
  `ℕ∞` and that `S_K(k + 1, s, f)` is finite
  ([refined strata](HenniartRefinedStrata.md)). Here `W_K` and `S_K` are the
  sets of unramified-twist orbits with given Swan exponent `s` and torsion
  number `f`, as defined there.
- `K.canonicalTopologicalData.ramificationIndex` is the natural number
  `v_K(p)`, the absolute ramification index `e_K`. The comparison `x < e_K`
  coerces it to `ℝ`.

### Remarks on the formal version

- Ranks are written `n = k + 1`, so every rank is positive. The injection
  hypothesis quantifies over exactly the ranks `1 ≤ n ≤ N`. The slope `x` is
  any real number and `N` any natural number. If `x < 0`, no natural `s`
  satisfies `s ≤ (k + 1) x`. If `N = 0`, there is no rank `k + 1 ≤ N`. In both
  cases the conclusion holds vacuously. This covers the route note's
  convention `x ≥ 0` and `N ≥ 1` for `C(L, x, N)`.
- The premises (I1) and (LD) are the published propositions. Each quantifies
  over all primes and all p-adic fields at the field universe `uK`, not only
  over `K`. This matches the route note: Proposition `prop:LDcount`
  (line 833), which the proof uses, assumes (LD) "for all p-adic fields".
  Theorem `thm:descent` (lines 1211–1213) assumes (I1) "for all p-adic
  fields `L`". Assuming (I1) for all fields rather than for `K` alone gives a
  stronger premise. The resulting implication is therefore no stronger than
  a version assuming (I1) for `K` only.
- The universes are independent. `uK` is the field universe, `uW` the Weil
  representation universe and `uV` the supercuspidal carrier universe. The
  premise (I1) is used at `uK, uV`, (LD) at `uK, uW`, and the conclusion at
  `uK, uW, uV`.
- The proposition contains no other hypotheses.
- The route note's Proposition `prop:basecase` adds a consequence: every
  numerical injection for `(L, n)` maps onto `{π : sw(π) < n e_L}`. That
  consequence is not part of this proposition. It comes from combining the
  conclusion with the counting-versus-surjectivity lemma, which the Library
  states as the first component of `CountingSurjectivityStatement`.

## Provenance

This conditional form is the route note's. It is not a statement printed in
Henniart's paper.

The source is the registered operator note
`operator-numerical-llc-route-2026-11-16`, *The numerical local Langlands
correspondence for GL_n: counts on the two sides and the recommended route of
proof*, 16 November 2026. Its directory is
`literature/Operator note - Numerical local Langlands for GL_n, counts on the two sides and the recommended route (16 November 2026)`,
with directory SHA-256
`faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`. The
locations below are in `numerical-LLC-route.tex`.

- §6.2, Proposition `prop:basecase` with its proof and the following remark
  (lines 1086–1094). The proposition is attributed to Henniart (1988),
  "Propositions 1.6 and 5.1", and marked "proved here from (I1) and (LD)".
  It reads: assume `|S_L(n,s,f)| ≤ ν(n,f,s;q_L)` for all `(n,s,f)` (input (I1))
  and that (LD) holds. If numerical injections for `(L,n)` exist for all
  `n ≤ N`, then `C(L,x,N)` holds for every `x < e_L`.
- §6.1, the definition of numerical injection (line 1049) and of
  `C(L,x,N)` (lines 1058–1061).
- §5.4, Proposition `prop:LD` (lines 820–830) and Proposition `prop:LDcount`
  (lines 832–847). §4.3, Remark `rem:upper` (lines 584–594), explains why the
  upper bound suffices once an injection exists.
- §7.1, item 4 (line 1307), lists this proposition for immediate release:
  "Proposition `prop:basecase`, conditional on (LD) and on the GL-side bound
  stated as a premise".

The route note's proof runs as follows. For `s < n e_L`, Proposition
`prop:LDcount` gives `ν(n,f,s;q_L) = |W_L(n,s,f)|`. The injection gives
`|W_L(n,s,f)| ≤ |S_L(n,s,f)|`, and (I1) gives `|S_L(n,s,f)| ≤ ν(n,f,s;q_L)`.
The condition `s ≤ n x` with `x < e_L` implies `s < n e_L`. That proof is
recorded here only as provenance. It is not formalized in this module, and
the Library does not prove the proposition.

The original results are in Guy Henniart, *La conjecture de Langlands locale
numérique pour GL(n)*, Ann. Sci. ÉNS (4) 21 (1988), 497–544. It is registered
as `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.

- Proposition 1.6, printed p. 500 (PDF p. 5). Let `φ_K` be an injection
  from `𝒢⁰_K(n)` to `𝒜⁰_K(n)` that is compatible with unramified twisting and
  preserves conductors. Then every `π ∈ 𝒜⁰_K(n)` with `s(π)/n < e` is in the
  image of `φ_K`. Here `e = v_K(p)` and `s(π)` is the Swan conductor.
- The proposition of §5.1, printed p. 512 (PDF p. 17), which the route note
  cites as Proposition 5.1. It makes the same assertion with the condition
  `s(π) < n e_K`. Henniart derives it "par le raisonnement de 2.8" from
  close-range Weil-side counts. These are `C_K(n,j) = (q_K − 1) q_K^j` for
  `0 ≤ j < n e` and the analogous counts over unramified extensions of `K`
  whose degree divides `n`. They are transported from characteristic `p`
  through Deligne's comparison of local fields with the same residue field.

Henniart's propositions conclude surjectivity in the close range. The
reasoning of his §2.8 (printed pp. 506–507) gets the GL-side number from the
Jacquet–Langlands correspondence (§§2.6–2.7) and Koch's computations. The
route note (line 1094) describes this as "the Jacquet–Langlands
correspondence and Koch's Anzahlsatz [2.8]". The route note makes two changes.
It replaces that exact count by the upper bound (I1), which comes from
Bushnell–Kutzko simple types. It also states the conclusion as the count
equality `C(L, x, N)` on refined strata. The Lean proposition encodes the
route note's form with the published Library declarations listed above.
