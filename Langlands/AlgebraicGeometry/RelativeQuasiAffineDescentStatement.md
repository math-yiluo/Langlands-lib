# Statements: descent of quasi-affine morphisms

This module states two Prop-valued descent
assertions for the predicate `Langlands.AlgebraicGeometry.IsQuasiAffineOver`
from [RelativeQuasiAffine](RelativeQuasiAffine.md). For `f : X ⟶ S`, that
predicate says that `f⁻¹(V)` is a quasi-affine scheme (Mathlib's
`Scheme.IsQuasiAffine`) for every affine open `V` of `S`. Both declarations
are proposition definitions, not proofs. Each states only the descent
direction: the predicate for the base changes implies it for `f`.

## The statements

`Langlands.AlgebraicGeometry.RelativeQuasiAffineFlatDescentStatement.{u}`
quantifies over schemes `X S S' : Scheme.{u}` in one arbitrary universe, a
morphism `f : X ⟶ S`, and a morphism `p : S' ⟶ S` with Mathlib's instances
`Flat p`, `QuasiCompact p` and `Surjective p`. It asserts that if
`IsQuasiAffineOver (pullback.snd f p)` holds, then `IsQuasiAffineOver f`
holds. Here `pullback.snd f p : pullback f p ⟶ S'` is the base change
`X ×_S S' ⟶ S'` of `f` along `p`. No hypothesis is placed on `X`, `S`,
`S'` or `f`.

`Langlands.AlgebraicGeometry.RelativeQuasiAffineEtaleDescentStatement.{u, v}`
quantifies over schemes `X S : Scheme.{u}`, a morphism `f : X ⟶ S`, and
`𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S`. Such a cover consists
of an index type `𝒰.I₀ : Type v` and morphisms `𝒰.f i : 𝒰.X i ⟶ S`.
Membership in `Scheme.precoverage @Etale` means that each `𝒰.f i` is etale
and that the family is jointly surjective. The index type is arbitrary and
may be infinite, and its universe `v` is independent of `u`. The statement
asserts that if `IsQuasiAffineOver (pullback.snd f (𝒰.f i))` holds for
every `i`, then `IsQuasiAffineOver f` holds. Here the morphism
`pullback.snd f (𝒰.f i)` is the base change `X ×_S 𝒰.X i ⟶ 𝒰.X i`.

## Source

The predicate is Stacks, Morphisms, Definition 29.13.1 (Tag 01SK). The
statements are the reflection direction of Stacks, Descent, Lemma 35.23.22
(Tag 02L7), on PDF p. 58 of the registered source
`stacks-descent-ed88ff78-2026`. That lemma says "The property P(f) = 'f is
quasi-affine' is fpqc local on the base." By Descent, Definition 35.22.1
(Tag 02KO, PDF p. 52), this means: for any fpqc covering `{Y_i → Y}` and
any `f : X → Y`, `f` has P if and only if each base change
`Y_i ×_Y X → Y_i` has P. The proof of Lemma 35.23.22 on p. 58 treats the
"if" direction. Only that direction is stated here.

Statement (1) is the case of the one-member covering `{p : S' → S}`. A
flat, quasi-compact, surjective morphism forms an fpqc covering. The
registered PDF says this in the proof of Descent, Lemma 35.25.1
(Tag 06NC, p. 61), and in Lemma 35.35.4 (Tag 0241, p. 83). Mathlib's
`QuasiCompact p` requires preimages of quasi-compact opens to be
quasi-compact. This is the usual notion of a quasi-compact morphism.

Statement (2) is the case of an etale covering. Each `𝒰.f i` is etale and
the family is jointly surjective, matching the definition of an etale
covering in Stacks, Topologies. Every etale covering is an fpqc covering.
The registered PDF recalls this on p. 87: "any τ-covering is also a
fpqc-covering", citing the results in Topologies. The Stacks index set
`I` is an arbitrary set. Correspondingly the Lean index type is arbitrary,
in its own universe `v`.

Lean's `pullback.snd f p` has source `pullback f p`, the fibre product
`X ×_S S'`. Stacks writes the factors in the other order, `Y_i ×_Y X`.
The two fibre products are canonically isomorphic over the base, and in
both cases the morphism is the projection to the base-change factor. So
the hypothesis is the same base change of `f` as in the source.

## Relation to Library results

The theorem
`Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent.quasiAffineOver_of_etaleCover`
proves statement (2) with this predicate written out. A private check
compiled the term
`fun f 𝒰 h => QuasiAffineEtaleDescent.quasiAffineOver_of_etaleCover f 𝒰 h`
as a proof of `RelativeQuasiAffineEtaleDescentStatement.{u, v}`. So statement
(2) adds no new proof obligation. This module only gives it a named
interface.

Statement (1) is proved for arbitrary bases by
`Langlands.AlgebraicGeometry.relativeQuasiAffineFlatDescent` in
[RelativeQuasiAffineFlatDescentProof](RelativeQuasiAffineFlatDescentProof.md).
The Library has results for affine bases:
`Langlands.AlgebraicGeometry.FaithfullyFlatQuasiAffineDescent.isQuasiAffine_of_isPullback`
treats one faithfully flat morphism between affine schemes, and
`Langlands.AlgebraicGeometry.QuasiAffineCoverDescent.isQuasiAffine_of_finite_affine_cover`
treats a finite jointly surjective flat family of affine schemes.
