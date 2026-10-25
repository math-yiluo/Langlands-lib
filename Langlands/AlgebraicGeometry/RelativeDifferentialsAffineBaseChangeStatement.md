# Canonical differential base change for spectra

`Langlands.Scheme.RelativeDifferentialsAffineBaseChangeIsIsoStatement.{u}` is a
Prop-valued definition. For every three commutative rings
`R A B : CommRingCat.{u}` and every pair of ring homomorphisms
`f : R ⟶ A` and `b : R ⟶ B`, it asserts

```text
IsIso (Langlands.Scheme.relativeDifferentialsBaseChangeMap
  (AlgebraicGeometry.Spec.map f) (AlgebraicGeometry.Spec.map b)).
```

The universe `u` is arbitrary. Zero rings are included, and there are no
smoothness, flatness, finiteness, nonemptiness, or additional affineness
hypotheses. No base-change witness is supplied as an assumption.

Write `F = AlgebraicGeometry.Spec.map f : Spec A ⟶ Spec R`,
`G = AlgebraicGeometry.Spec.map b : Spec B ⟶ Spec R`,
`P = CategoryTheory.Limits.pullback F G`,
`p = CategoryTheory.Limits.pullback.fst F G`, and
`q = CategoryTheory.Limits.pullback.snd F G`. The map in the proposition is the
actual imported morphism

```text
(AlgebraicGeometry.Scheme.Modules.pullback p).obj
  (Langlands.Scheme.relativeDifferentials F)
    ⟶ Langlands.Scheme.relativeDifferentials q.
```

In particular, its domain and codomain are module sheaves on the categorical
scheme pullback `P`. The construction specializes
`relativeDifferentialsSquareMap` and uses universal derivations and the module
pullback/pushforward adjunction. Its adjoint sends the universal differential
of a local section `a` on an open `U` of `Spec A` to the universal differential
of `p.app U a` on `p ⁻¹ᵁ U`. The imported
`relativeDifferentialsBaseChangeMap_adjoint_app` proves this formula and
`relativeDifferentialsBaseChangeMap_unique_of_app` proves uniqueness from it.
The proposition therefore concerns this concrete canonical comparison.

This module supplies a statement to be proved. It supplies no proof or
isomorphism instance and leaves the imported constructions and existing
statement modules unchanged. Its affine target is a prerequisite for local
assembly of the separate arbitrary-scheme base-change theorem.

## Source and formal proof boundary

Stacks Project Lemma 29.33.10 (tag
[01V0](https://stacks.math.columbia.edu/tag/01V0)) asserts that the canonical map
of Lemma 29.33.8 (tag
[01UV](https://stacks.math.columbia.edu/tag/01UV)) is invertible after arbitrary
scheme base change. Specialize `X = Spec A`, `S = Spec R`, and `S' = Spec B`,
with structural maps induced by `f` and `b`. Then its `X'` is the categorical
scheme pullback `P` above and its projection `g'` is `p`, giving exactly the
scope of this proposition. The characterization on differentials in 01UV
matches the imported local-section formula.

Both originals and their proofs were read in `01UM.html`, lines 321–371, in
registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
the retained HTML snapshot of 2026-10-21, directory content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
No relevant errata file was present in the public notes consulted.

The proof of 01V0 refers to the sheafified ring-level base-change result,
Algebra Lemma 10.131.12 (tag 00RV). A separate formal proof must identify the
scheme pullback with the spectrum of the ring pushout and show compatibility
of the concrete canonical comparison with the differential module
base-change isomorphism. The intended route reuses the Spec differential
comparison, the canonical tilde pullback/scalar-extension construction, and
Mathlib's `KaehlerDifferential.tensorKaehlerEquiv` with its differential
formula `KaehlerDifferential.tensorKaehlerEquiv_tmul_D`. None of those proof
steps or the parent arbitrary-scheme theorem is assumed by this statement.
