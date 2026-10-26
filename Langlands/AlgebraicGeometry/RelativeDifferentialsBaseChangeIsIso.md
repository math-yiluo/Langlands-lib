# Arbitrary base change for the canonical relative differential sheaf map

`Langlands.Scheme.relativeDifferentialsBaseChangeIsIso` proves the exact
published proposition
`Langlands.Scheme.RelativeDifferentialsBaseChangeIsIsoStatement S` for every
`S : AlgebraicGeometry.Scheme.{u}`, with arbitrary universe `u`.
For every pair of schemes `X` and `T` and every pair of morphisms
`f : X ⟶ S` and `b : T ⟶ S`, the conclusion is
`IsIso (Langlands.Scheme.relativeDifferentialsBaseChangeMap f b)`.
The complete theorem telescope is

```text
(S : AlgebraicGeometry.Scheme.{u}) : RelativeDifferentialsBaseChangeIsIsoStatement S.
```

The comparison is the actual published morphism from the pullback of
`relativeDifferentials f` along `Limits.pullback.fst f b` to
`relativeDifferentials (Limits.pullback.snd f b)` on the categorical scheme
pullback. There are no smoothness, flatness, finiteness, nonemptiness,
affineness, or supplied base-change hypotheses. The target statement and
the canonical construction are imported unchanged.

The proof applies
`relativeDifferentialsBaseChangeIsIso_of_local_inputs` from the companion
`RelativeDifferentialsBaseChangeProof` module. It supplies the published
`relativeDifferentialsOpenImmersionIsIso` and
`relativeDifferentialsAffineBaseChangeIsIso`, imported from
`RelativeDifferentialsOpenImmersionProof` and
`RelativeDifferentialsAffineBaseChangeProof` respectively. Thus no local
comparison premise remains in the final theorem.

The reduction first passes from spectra to arbitrary affine schemes using
`isoSpec` and naturality. It next covers both sources over an affine base,
then covers the base by affine opens. At each step, composition and
congruence for canonical square maps identify the local comparison with
the pullback of the original map. Open-immersion locality and detection of
isomorphisms on an open cover finish the passage. The companion Markdown
describes these steps and their pullback coherence factors.

The imported affine proof identifies the canonical square map with the
tensor Kähler-differential isomorphism by checking universal differential
generators after adjunction. It uses the published spectral comparison,
the canonical tilde-pullback comparison and its generator formula, and
Mathlib's tensor-spectrum model of the categorical pullback. Its own
paired explanation describes these calculations. The current two modules
import those results rather than redeclaring their proofs.

The source assertion is Stacks Project Lemma 29.33.10 (tag
[01V0](https://stacks.math.columbia.edu/tag/01V0)), whose map is the one
characterized in Lemma 29.33.8 (tag
[01UV](https://stacks.math.columbia.edu/tag/01UV)). Both originals and their
proofs were read in `01UM.html`, lines 321–371, of registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, directory content
SHA256 `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
No relevant public erratum was present in the consulted Library. The source
proves the assertion by sheafifying algebraic base change; the implemented
route makes the affine comparison and the local-to-global transport
explicit. The global reduction and this final assembly were authored by
Worker 208. Worker 274 contributed the comparisons used during development
of the assembled proof; these now enter through their published modules.
