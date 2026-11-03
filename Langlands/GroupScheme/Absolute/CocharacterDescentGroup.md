# Group-scheme recovery for invariant cocharacters

Worker 1272.

This derived construction completes the group-scheme descent step begun in
`CocharacterDescent`. Its source motivation is the descent of the invariant
cocharacter in the converse of Milne, *Algebraic Groups* (2017), Theorem 25.1,
printed page 544 (PDF page 560). The explicit Laurent-point comparison and
reflection argument below are internal implementation choices, rather than
separate assertions attributed to that theorem.

Let `k` and `K` be fields in the same universe with a `k`-algebra structure on
`K`, and let `G` be a group scheme over `Spec k`. For the construction `descend`,
assume that `K/k` is finite dimensional and Galois, that `G` is affine over
`Spec k`, and that the given group-scheme homomorphism `ν : Gm_K ⟶ G_K` is fixed
by every published `transportCocharacter` for `Gal(K/k)`. Invariance is precisely
the proposition `GaloisCocharacterDescent.IsInvariant`.

The definition `descend` is an actual group-scheme homomorphism `Gm_k ⟶ G`.
The theorem `baseChange_descend` proves that its base change, precomposed with
the inverse of the canonical multiplicative-group base-change isomorphism, is
the original `ν`. No torus, finite type, smoothness, reductivity, perfectness, or
characteristic assumption is needed.

The implementation has three steps.

1. `extendTest` is the morphism of relative Laurent test schemes induced by
   extension of coefficients from `k` to `K`, with the extension-field structure
   restricted to `k`. Its underlying scheme morphism is the spectrum of
   `LaurentGaloisDescent.extend`. The theorem `extendTest_universalUnit` proves
   that this morphism preserves the universal Laurent unit by naturality of
   global sections and the coefficient-extension formula on Laurent monomials.
   `baseChangeIso_universalProjection` then identifies the projection of the
   universal point through the multiplicative-group comparison isomorphism.

2. `baseChangedMorphism` applies ordinary scheme pullback to any underlying
   morphism `Gm_k.X ⟶ G.X` and precomposes with that comparison isomorphism.
   `baseChangePointsEquiv_morphism` proves naturality of the point adjunction
   for an arbitrary underlying morphism. These comparisons show that the
   universal Laurent value of `baseChangedMorphism` extends the original
   Laurent coefficients. Applying the existing identity
   `extend_descendedPoint`, and cancelling the Laurent presentation and point
   equivalences, proves `baseChangedMorphism_descendedMorphism`.
   `pullback_descendedMorphism` restates this equality before the
   multiplicative-group comparison.

3. `faithful_algebraPullback` proves that scheme pullback along `Spec K ⟶
   Spec k` is faithful. A field extension is faithfully flat, hence the spectrum
   morphism is flat and surjective; the existing affine quasi-compactness and
   flat-descent instances give faithfulness. The generic lemma
   `isMonHom_of_faithfulMap` reflects the unit and multiplication equations
   through a faithful monoidal functor, using the functor's unit and tensor
   comparison maps. The recovered pullback is a composite of known group
   homomorphisms. Consequently `descendedMorphism_isMonHom` proves the group
   laws for the descended scheme morphism, and `Grp.homMk` bundles it as
   `descend`. Extensionality of bundled group morphisms gives
   `baseChange_descend`.

The coefficient-extension comparisons, faithfulness, and reflection lemma have
only the hypotheses visible in their declarations; finite Galois and
affineness hypotheses enter when using the preceding coordinate-descent
construction. This module proves recovery and preservation of the group laws;
the parabolic classification still requires its structural and subgroup
comparison arguments.
