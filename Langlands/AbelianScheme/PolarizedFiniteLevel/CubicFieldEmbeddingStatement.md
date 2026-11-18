# The cubic Lefschetz embedding of an ordinary polarized datum over a field

`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingStatement`
is a proposition definition with universe parameter `u`. It is a statement
target only; this module proves nothing.

## The statement

Let `P : Prerequisites.{u}` be the published prerequisites. Let `K : Type u`
be a field, let `g d n` be natural numbers with `0 < d`, and let
`a : Datum P (Spec K) g d n` be an actual ordinary polarized datum over
`Spec K`. Write `π = a.abelian.X.hom : A → Spec K` for its abelian variety and
`L³ = a.cubicBundle`. This is the actual third tensor power of the canonical
diagonal Poincaré bundle `a.canonicalBundle`, the bundle `L^Δ(λ)` of
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, Definition 7.5. The
proposition asserts the following two facts.

1. `Epi a.cubicEvaluationAdjoint`. This morphism is the actual adjunction
   counit `π^* π_* L³ → L³` of `O_A`-modules. Its epimorphy says that the
   complete linear system of `L³` has no base points.
2. Fix a natural number `m` and a `K`-basis
   `b : Module.Basis (Fin (m + 1)) K H` of
   `H = (relativeGlobalSections π).obj L³`. This is the `K`-module of global
   sections of `L³`, namely the pushforward to `Spec K` followed by the
   global-sections functor of `Spec K`. Also fix a proof `hb` that every point
   `x` of `A` lies in `nonvanishingLocus L³ (b i)` for some `i`, that is,
   `b i` has nonzero value in the residue-field fibre at `x`. Then
   `relativeLinearSystemMap π hb : A → RelativeProjectiveSpace (Spec K) m`
   is a closed immersion. This is the published morphism to relative
   projective `m`-space defined by the sections `b 0, …, b m`.

The no-common-zero proof `hb` is an argument and not an extra restriction:
by the first assertion, the sections of any basis have no common zero. The
proposition is stated for every basis, so it does not depend on a choice of
coordinates. In particular, together with the published
`CubicDirectImageStatement` (rank `6^g·d`), it gives a closed immersion of
`A` into `ℙ^{6^g·d − 1}_K`.

The hypothesis `0 < d` matches the published `Datum.cubicProjectiveEvaluation`,
where this statement is to be used. It only weakens the proposition.

## Provenance

The mathematical content is Lefschetz's theorem in the form of Mumford,
*Abelian Varieties* (1970), §17 "Very ample line bundles", Theorem, printed
p.163 (PDF p.86 of the registered scan
`mumford-abelian-varieties-full-scan`): for an ample line bundle `L` on an
abelian variety `X`, `L^n` is very ample if `n ≥ 3`. Mumford writes out the
proof for `L³`. The proof reduces to two claims, stated on that page and
proved on the following pages: the complete linear system `|3D|` separates
points (claim (1)) and tangent vectors (claim (2)). So the complete linear
system of `L³` has no base points and defines a closed immersion. A morphism defined by a different basis of the same space
of sections differs by a linear automorphism of projective space. Hence
every basis in assertion 2 gives a closed immersion.

The ampleness input is the published `CanonicalCubicBundleAmpleStatement`:
the canonical diagonal bundle of every datum over every field is ample.
GIT §7.2, printed p.131 (PDF p.144 of the registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`),
uses exactly this embedding of `X` by the sections of `L^Δ(ω)³`, with
`m = 6^g·d − 1`.

Mumford works over an algebraically closed field. The present statement over
an arbitrary field `K` is a standard derived consequence. Let `K̄` be an
algebraic closure. By flat base change (Stacks Project, Lemma 30.5.2,
tag 02KH, registered as
`stacks-flat-base-change-projection-formula-2026-11-02`), `π_* L³` commutes
with base change to `K̄`. So the counit and a basis of global sections base
change to the counit and a basis over `K̄`. Epimorphy of a map of
quasi-coherent sheaves can be checked after the faithfully flat base change
`Spec K̄ → Spec K`. The property of being a closed immersion is fpqc local on
the base (Stacks Project, *Descent*, Lemma 35.23.21, tag 02L6, PDF p.58 of
the registered `stacks-descent-ed88ff78-2026`). Ampleness over `K̄` is again
supplied by `CanonicalCubicBundleAmpleStatement`.

The statement uses the published Library objects `Datum`,
`Datum.cubicBundle`, `Datum.cubicEvaluationAdjoint` (module
`CubicEvaluation`), `relativeGlobalSections`, `nonvanishingLocus` and
`relativeLinearSystemMap` (module `LinearSystem/RelativeMorphism`). It
introduces no new construction.
