# Induced maps on relative differential sheaves

For arbitrary schemes `X`, `Y`, and `S` in universe `u`, a morphism
`g : X ⟶ Y`, structure maps `fX : X ⟶ S` and `fY : Y ⟶ S`, and a
commuting triangle `w : g ≫ fY = fX`, this module constructs

`relativeDifferentialsMap g w : (Modules.pullback g).obj (relativeDifferentials fY) ⟶ relativeDifferentials fX`.

Both differential sheaves and the pullback functor are actual objects and
functors in Mathlib's categories of module sheaves. There are no smoothness,
affineness, flatness, or quasicoherence hypotheses.

The construction first precomposes the distinguished derivation on `X` with
the local section maps of `g`. The result is a relative derivation on `Y`
with values in the actual pushforward of the differential sheaf on `X`.
`relativeDifferentialsPushforwardMap g w` is its descent along the proved
universal property of the concrete differential sheaf on `Y`.
`relativeDifferentialsMap` is its inverse image under the hom equivalence of
Mathlib's `pullbackPushforwardAdjunction g`. The universal property is proved
in the imported module, not supplied as an assumption.

The factorization lemmas identify the descended and adjoint maps on the
universal derivations. In particular, `relativeDifferentialsMap_adjoint_app`
states on every open `U` of `Y` and section `a` that the adjoint sends
`d_Y(a)` to `d_X(g.app U a)` on the inverse-image open. This follows by
evaluating the derivation equality, using the local formula for precomposition.
`relativeDifferentialsMap_unique` proves that this derivation equality uniquely
determines the pullback morphism: apply injectivity of the adjunction hom
equivalence and then uniqueness from the universal differential sheaf.

The source is Stacks Project, Section 17.28, Lemma 17.28.12 (tag 08RU),
specialized to schemes over a fixed base and the identity map on that base.
Its first construction gives precisely the pushforward map used here, and
its adjunction statement gives the displayed pullback map and local
characterization. Scheme specialization is Definition 29.33.1 (tag 01UM).
Registered source: `stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
files `08RL.html` and `01UM.html`.

The separate `RelativeDifferentialsMapsStatement` and
`RelativeDifferentialsMapsCoherence` modules state and prove the identity and
composition laws. No base-change isomorphism or local-freeness claim is made.
