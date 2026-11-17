# Counting Bushnell–Kutzko labels by the polar-part number

`Langlands.Henniart.BushnellKutzkoLabelCountStatement : Prop` states the identification of
label sets in Lemma `lem:BKlabels` of the operator route note *Numerical local Langlands for
GL_n: counts on the two sides and the recommended route* (16 November 2026, registered
literature `operator-numerical-llc-route-2026-11-16`; §4.3, lemma and proof at lines 538–556
of `numerical-LLC-route.tex`), in counting form.

## Provenance

Lemma `lem:BKlabels` is an internal result of the route note ("proved here"), not a
numbered result of Bushnell–Kutzko 1994 (BK94). BK94 itself, in §3 after (3.10) (printed
p. 127), says that its count of discrete series representations agrees with the one obtained
from Koch's work and the Matching Theorem of Deligne–Kazhdan–Vignéras, and leaves that check
to the reader; the route note's lemma, together with its Lemma `lem:polar`, carries out that
check.

## Objects

- `Langlands.BushnellKutzko.extendedLabelSet m a b q` is BK94's `P̃_m(a, b; q)` (printed
  p. 125), built from `P_m(a, b; q) = P^0_m(a, b; q)` of (1.13) (printed pp. 115–116):
  pairs `(p, φ)` of a label `p` and a polynomial `φ ∈ 𝔍(f(p), q^{d(p)})`.
- `Label.e p = e(p)` (BK94, printed p. 116), the last of the numbers `e_i` of the label.
- `Langlands.BushnellKutzko.degenerateLabelSet b q` is `P̃_0(a, b; q) = 𝔍(b, q)` (BK94,
  printed p. 126); it does not depend on `a`.
- `Langlands.Henniart.Numerical.polarPartCount q n f s` is the polar-part number
  `ν(n, f, s; q)` of the route note (Definition `def:model`), published by Task 7369: the
  number of `Gal(𝔽_{q^f}/𝔽_q)`-orbits of maps `c : {0, …, s/f} → 𝔽_{q^f}` with `c 0 ≠ 0`,
  `c (s/f) ≠ 0`, values generating `𝔽_{q^f}` over `𝔽_q`, and
  `gcd(n/f, {i ≥ 1 : c i ≠ 0}) = 1`.

The definitions of the label sets, of `e`, and of the fields `𝔽_{q^D}` are explained in
`Langlands/BushnellKutzko/Labels.md`.

The fields `𝔽_{q^D}` are `polarExtensionField (labelFieldSize q) D` (see the labels
Markdown). For a prime power `q`, `labelFieldSize q = q`, so these are the fields that
Task 7369 uses for `polarPartCount` (module `Langlands.Correspondence.HenniartPolarPart`).
The label sets take no instance argument on `q`, so the statement quantifies directly over
prime powers `q`.

## Statement

For every prime power `q` and all natural numbers `n ≥ 1`, `f ≥ 1` with `f ∣ n`:

1. for every `m ≥ 1`, the set
   `{(p, φ) ∈ P̃_m(n/f, f; q) : e(p) = 1}` has exactly `ν(n, f, f m; q)` elements. Here the
   label set has top level `m`, bottom level `0`, `a = n/f` and `b = f`. In the route note
   this is the bijection between these labels and the polar-part set `PP(n, f, f m; q)`;
   the note writes `P_m(t, n/t; q)` with `t = n/f` for BK94's `P^0_m(t, n/t; q)`.
2. `P̃_0(1, n; q) = 𝔍(n, q)` has exactly `ν(n, n, 0; q)` elements (the case `m = 0` of the
   lemma).

Both cardinalities are `Set.encard` values in `ℕ∞`, compared with the natural number
`polarPartCount …` cast to `ℕ∞`; so each statement also asserts that the set is finite. No
finiteness hypothesis is assumed. Natural-number division `n / f` is exact because `f ∣ n`.

## Proof idea (route note, proof of Lemma `lem:BKlabels`)

Not part of this record; the proof is a separate task. "Take roots successively": to a
label `((φ_i, n_i, d_i, e_i))_{0 ≤ i ≤ r}` with `φ` attach the map `c` with `c(n_i)` a root of
`φ_i` and `c(0)` a root of `φ`, roots being taken successively in the tower
`𝔽_q ⊆ 𝔽_{q^{d_0}} ⊆ 𝔽_{q^{d_0 d_1}} ⊆ ⋯ ⊆ 𝔽_{q^f}`, and `c = 0` elsewhere. The degree
conditions say exactly that the values of `c` generate `𝔽_{q^f}`; sequences of polynomials
correspond to Galois orbits of the root tuples (both sides have
`∏ |𝔍(d_i, q^{d_0 ⋯ d_{i−1}})| · |𝔍(f/d(p), q^{d(p)})|` elements for each choice of levels
and degrees); and `e(p) = gcd(n/f, n_0, …, n_r)`, so `e(p) = 1` is condition (P3) of the
polar-part model. For `m = 0`, both sides count the monic irreducible polynomials of
degree `n` over `𝔽_q` other than `X`.

Sanity check from the task context: for `n = f = 1` both sides of part 1 equal
`(q − 1)^2 q^{m−1}`.
