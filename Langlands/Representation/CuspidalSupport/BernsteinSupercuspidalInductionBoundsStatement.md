# Numerical bounds for induction from supercuspidal representations: statement

Module `Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalInductionBoundsStatement`.
Namespace `Langlands.CuspidalSupport`.
Entry proposition `BernsteinSupercuspidalInductionBoundsStatement`; nothing is proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.4.1–V.4.4 (printed pp.118–119 / PDF pp.124–125) and
VI.5.2–VI.5.4 (printed pp.172–175 / PDF pp.178–181).

The Theorem of VI.5.4 (printed pp.173–174 / PDF pp.179–180) contains two
numerical bounds:

> **Théorème.** Soient `P = MN` un sous-groupe parabolique de `G`, `(ρ, W)` une
> représentation supercuspidale irréductible de `M` et `(π, V) = i_P^G(ρ, W)`.
> Alors la représentation `π` est de longueur finie, plus petite ou égale à
> `l(M)`. […] Enfin si l'on suppose `P` et `P′` standards, et que l'on pose
> `W(ρ, ρ′) = {w ∈ W_G | w · M = M′, ʷρ′ = ρ}`, alors
> `dim Hom_G(π, π′) ≤ |W_M \ W(ρ, ρ′)|`.

Here `π′ = i_{P′}^G(ρ′)` for a second parabolic `P′ = M′N′` and an irreducible
supercuspidal `ρ′` of `M′`. The notation is that of V.4:

- `W_G = N_G(A_∅)/Z_G(A_∅)` (V.4.1), and `W_M = N_M(A_∅)/Z_M(A_∅)`, which
  injects into `W_G` (V.4.3.1);
- for `w ∈ W_G` with representative `g` and a standard Levi `M`,
  `w · M = gMg⁻¹`, independent of the representative (V.4.3);
- `W(L, M) = {w ∈ W_G | w · L = M}` (V.4.3.2), `W(M, ∗) = ⋃_L W(M, L)` over
  the standard Levis `L`, and `l(M) = |W_M \ W(∗, M)| = |W(M, ∗)/W_M|`
  (V.4.4, printed p.119 / PDF p.125); for a non-standard `M`, `l(M) = l(M′)`
  for a standard Levi `M′` conjugate to `M`.

The published `LeviSupercuspidalInductionAssociationStatement` (VI.5.4,
Theorem, for arbitrary actual parabolics) states finite length and the four
equivalent conditions, and explicitly leaves out these two bounds. This unit
states them.

## The objects

All objects are published; this file constructs nothing. The setting is the
standard-family framework of Worker 1153 (modules `BernsteinData` and
`BernsteinBlock`), with the binders of the published VI.7.2 statement units.

- `F`, `G`, `T`, `i`, `ν` and `family : BernsteinStandardFamily i ν`: a
  nonarchimedean local field, a group scheme with locally compact
  nonarchimedean `G(F)` in the canonical topology, and the actual standard
  family (connected reductive `G`, maximal split torus `i`, generic
  cocharacter `ν`, structural hypotheses only).
- A cuspidal datum `a : BernsteinCuspidalDatum.{uF, uV} i ν family` is a
  standard Levi `M = levi i ν a.roots` with an irreducible smooth
  representation `ρ = a.representation` whose proper standard Jacquet modules
  vanish, which is Renard's supercuspidality (VI.2.1, Definition and Remark 1,
  printed p.137 / PDF p.143). `P` is its standard parabolic, and
  `i_P^G(ρ)` is the published `bernsteinInduction i ν family a`.
- `W_G` is the published `Weyl i`: the normalizer of the torus image
  `torusPoints i` (the rational points `A_∅(F)` of the maximal split torus) in
  `G(F)`, modulo its full centralizer. `W_M` is `WL a.roots`, the range of the
  published injective homomorphism `Group.RelativeWeyl.inclusion` from the
  quotient `(N_G(A_∅) ∩ M) / (Z_G(A_∅) ∩ M)`.
- `w · M = L` is expressed as: some `n` in the normalizer with image `w`
  satisfies `(levi i ν a.roots).map (MulAut.conj n) = levi i ν K`, the Levi of
  `L` being `levi i ν K`.
- `ʷρ′ = ρ` is expressed through the representations on the literal Levi
  subgroups (`bernsteinLiteralLeviRep`): a linear isomorphism `e` from the
  space of `ρ` to that of `ρ′` with `e(ρ(m)x) = ρ′(n m n⁻¹)(e x)` for all
  `m ∈ M(F)`, where `n m n⁻¹` is computed by the published
  `Group.RelativeWeyl.conjugationEquiv`. This says `ρ′ ∘ Ad(n) ≃ ρ`, which is
  `ʷρ′ ≃ ρ`: since `w · M = M′`, the representation `ʷρ′` of `M` is
  `m ↦ ρ′(n m n⁻¹)`. Representations are compared up to isomorphism, as in the
  association of cuspidal data (VI.5.2).
- The length is the published `HasCompositionLengthAtMost`, applied to the
  underlying representation (`SmoothRep.toRep`): there is a composition series
  with at most the given number of factors.
- `dim Hom_G(π, π′)` is `Module.rank ℂ` of the space of intertwiners
  `(bernsteinInduction a).representation.IntertwiningMap
  (bernsteinInduction a′).representation`, a cardinal, so no finite
  dimensionality is presupposed.

## The Lean statement

`BernsteinSupercuspidalInductionBoundsStatement` quantifies over the data above
and asserts:

1. for every cuspidal datum `a`, `i_P^G(ρ)` has a composition series of length
   at most `Nat.card` of the image in `W_G ⧸ W_M` of
   `{w | ∃ K, w · M = levi i ν K}`, that is, `|W(M, ∗)/W_M| = l(M)`;
2. for all cuspidal data `a`, `a′`, the rank of the intertwiner space
   `i_P^G(ρ) → i_{P′}^G(ρ′)` is at most `Nat.card` of the image in `W_G ⧸ W_M`
   of `{w | w · M = M′ and ʷρ′ ≃ ρ}`.

## Formal choices

- **Standard data.** Both bounds are stated for standard parabolics. For the
  dimension bound, so does Renard. For the length bound, an arbitrary `P = MN`
  is `G(F)`-conjugate to a standard one, conjugation transports `i_P^G(ρ)`, and
  `l(M)` is defined through the standard conjugate.
- **`l(M)` as `|W(M, ∗)/W_M|`.** Renard gives both expressions
  `|W_M \ W(∗, M)| = |W(M, ∗)/W_M|`. The statement uses the second. The set
  `W(M, ∗)` is stable under right multiplication by `W_M`, so its image in
  `W_G ⧸ W_M` is its set of left cosets.
- **The orbit count in the dimension bound.** Renard writes
  `|W_M \ W(ρ, ρ′)|`. With `w · M = M′` and `ʷρ′ = ρ`, the set `W(ρ, ρ′)` is
  stable under right multiplication by `W_M` (a representative `m ∈ M` of
  `v ∈ W_M` gives `ʷᵛρ′ = ᵛ(ʷρ′) ≃ ᵛρ ≃ ρ`), and under left multiplication
  by `W_{M′}`, but in general not under left multiplication by `W_M`. The
  statement counts the left cosets `w W_M`, which is `|W(ρ, ρ′)|/|W_M|`,
  equal to `|W_{M′} \ W(ρ, ρ′)|` because `W_M` and `W_{M′}` are conjugate. This
  is the number the proof produces: by (VI.5.4.1) and VI.5.3 (iii) the
  intertwiners are bounded by the number of graded pieces `ʷρ ≃ ρ′` of
  `r_{P′}^G i_P^G(ρ)`, indexed by `W(M′, M)/W_{M′}`.
- **Representatives.** Renard's `w · M` does not depend on the representative
  because `Z_G(A_∅) = M_∅ ⊆ M`. The statement asks for some representative
  with the property, which is the same set. The published `Weyl i` uses the
  centralizer of `A_∅(F)` in `G(F)`; it equals `M_∅(F)` because `A_∅(F)` is
  Zariski dense in the split torus `A_∅`. This comparison is not formalized
  here and is not needed to read the statement.
- **Cardinalities.** `W_G` is finite (V.4.1), so the sets counted by
  `Nat.card` are finite and `Nat.card` is their number of elements. The
  finiteness of `Weyl i` is not a premise of the statement.
- **Universe.** The representations `ρ`, `ρ′` have carriers in an arbitrary
  universe `uV`; the induced representations have carriers in `max uF uV`, as
  in the published `bernsteinInduction`.

## Scope

This file states the two bounds of the VI.5.4 Theorem and proves nothing. A
proof belongs to a separate `lean.proof@1` task targeting
`BernsteinSupercuspidalInductionBoundsStatement`. The source proves the length
bound with the additive function `l′(τ) = Σ_{L ∼ M} l(r_Q^G τ)` and the
filtration of VI.5.3 (iii), and the dimension bound with Frobenius
reciprocity (VI.5.4.1) and the same filtration. The finite-length assertion
and the equivalence of the four conditions are the published
`LeviSupercuspidalInductionAssociationStatement`.

The file imports `Langlands.Representation.CuspidalSupport.BernsteinBlock` and
`Langlands.Representation.Filtration.ObjectDefinitions` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
