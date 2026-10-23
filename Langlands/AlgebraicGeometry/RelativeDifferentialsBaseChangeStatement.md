# Arbitrary base change for relative differentials

`Langlands.Scheme.RelativeDifferentialsBaseChangeIsIsoStatement S` is a
Prop-valued definition. For every pair of schemes `X` and `T`, every morphism
`f : X ⟶ S`, and every morphism `b : T ⟶ S`, it asserts
`IsIso (Langlands.Scheme.relativeDifferentialsBaseChangeMap f b)`.
The parameter `S` and the quantified schemes `X` and `T` all lie in the
same arbitrary universe `u`. There are no smoothness, flatness, finiteness,
affineness, or other additional hypotheses.

Write `X' = Limits.pullback f b`, `p = Limits.pullback.fst f b`, and
`f' = Limits.pullback.snd f b`. The map in the proposition is the actual
imported morphism

```text
(AlgebraicGeometry.Scheme.Modules.pullback p).obj
  (Langlands.Scheme.relativeDifferentials f)
    ⟶ Langlands.Scheme.relativeDifferentials f'.
```

The imported construction specializes `relativeDifferentialsSquareMap` to
the categorical scheme fiber product. It uses the universal derivation of
the concrete sheafified relative differentials and the module
pullback/pushforward adjunction. Its adjoint sends the universal differential
of each local section `a` on an open `U` of `X` to the universal differential
of `p.app U a` on `p ⁻¹ᵁ U`; the imported
`relativeDifferentialsBaseChangeMap_adjoint_app` gives this formula and
`relativeDifferentialsBaseChangeMap_unique_of_app` gives uniqueness.
Thus the proposition concerns the canonical comparison itself.

This module states invertibility as a proposition to be proved. It supplies
neither a proof nor an isomorphism instance, and assumes no base-change witness.
It imports the published construction without changing it.

## Source

The statement translates Stacks Project Lemma 29.33.10 (tag
[01V0](https://stacks.math.columbia.edu/tag/01V0)), whose map is the canonical
map of Lemma 29.33.8 (tag
[01UV](https://stacks.math.columbia.edu/tag/01UV)). With the source's
`S' = T` and projection `g' = p`, the source asserts exactly that
`p* Ω_(X/S) ⟶ Ω_(X'/T)` is an isomorphism for arbitrary scheme morphisms.
Lemma 29.33.8 constructs this map by universal derivations and adjunction
and characterizes it on differentials of local sections, matching the
imported characterization above. Lemma 29.33.10 refers to the sheafified
ring-level base-change lemma for its proof; that proof is outside this
statement module.

Both originals and their proofs were read in `01UM.html`, lines 321–371,
of registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
the retained HTML snapshot of 2026-10-21. The registered source-directory
content SHA256 is
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
