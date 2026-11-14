# Rational surjectivity of torus quotients with torus kernel

`Langlands.GroupScheme.TorusQuotientRationalSurjectivityStatement.{u}` is an
unproved proposition. It isolates the rational-point step in the proof of
Kaletha–Prasad Corollary B.8.6. This module supplies no proof.

## Exact formulation

Let `k : Type u` be a field satisfying `HasTrivialTorusCocycles k`: for every
torus `T` over `Spec k` and every finite Galois extension `L/k` in universe
`u`, every actual torus cocycle of `T` for the cover `Spec L → Spec k` is a
coboundary. Let `B` and `C` be group schemes over `Spec k` which are tori,
and let `q : B ⟶ C` be a homomorphism. Assume the underlying scheme map of
`q` is surjective and the full scheme-theoretic kernel `kernel q` (the
pullback of `q` along the unit section of `C`) is a torus. The conclusion is
that the induced homomorphism of rational points

```text
rationalPoints.map q : B(k) → C(k)
```

is surjective.

The hypotheses encode an exact sequence `1 → A → B → C → 1` of `k`-tori with
`A = kernel q`; no chosen subgroup of the kernel is substituted. No
affineness, splitting or dimension assumption is added. The statement is at
arbitrary universe `u`.

## Source and provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The first sentence of the proof of Corollary B.8.6, printed p. 683 / PDF
p. 714, states that the sequence of `K̂`-points of an exact sequence of tori
is exact "due to Lemma 2.5.4 and Example 2.3.2". Lemma 2.5.4, printed p. 87 /
PDF p. 118, asserts that `H^i(F, T)` vanishes for every `F`-torus `T` and
`i > 0` when `dim(F) ≤ 1`. Example 2.3.2, printed p. 79 / PDF p. 110, says
that maximal unramified extensions satisfy this condition. The cited step
is the long exact cohomology sequence
`B(F) → C(F) → H^1(F, A) = 1`.

This statement is derived from that step. It replaces the condition
`dim(F) ≤ 1` by the Library's cocycle condition `HasTrivialTorusCocycles`,
which is exactly what the cohomological argument uses. The Library proves
that `HasDimensionLEOne K` implies `HasTrivialTorusCocycles K`
(`dimensionLEOneTorusCocycleVanishing`). It also proves that the maximal
unramified extension of a nonarchimedean local field has dimension at most
one (`Langlands.FieldTheory.henselianDiscreteDimensionLEOne`). Thus the
statement applies over that field, which is the case used by the B.8.6
assembly.

## Remaining proof obligation

A proof must show that the fibre of `q` over a rational point is a torsor
under `kernel q`, trivialize it over a finite Galois extension, and use the
vanishing of the resulting torus cocycle to descend a point to `k`.
