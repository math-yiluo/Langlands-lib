# Representability of a space morphism from one represented atlas pullback

This helper module (namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasEffectivity`) supplies the
representability half of
`Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityStatement`.
The entry module `RepresentedAtlasEffectivityProof.lean` uses it. It contains
no statements, only proved lemmas, and it adds no hypotheses to the target.

Throughout, `h := schemeYoneda S`. The atlas data are a morphism `f : X ⟶ Y` of
algebraic spaces, a surjective étale `b : h V ⟶ Y`, a scheme map `q : U ⟶ V`
over `S` and a cartesian square
`hsq : IsPullback a (h.map q) (hom f) b`. A scheme test is a map
`g : h T ⟶ Y`. Its fppf-sheaf pullback is `F` with
`hF : IsPullback φ₁ φ₂ (hom f) g`.

## Plumbing

- `exists_app_of_isPullback`: sections of a presheaf pullback are pairs of
  sections with equal images (evaluate the square and use
  `Types.exists_of_isPullback`).
- `exists_sheaf_isPullback`: two maps of fppf sheaves have a pullback in fppf
  sheaves whose underlying presheaf square is cartesian (sheaves have limits and
  `sheafToPresheaf` preserves them).
- `exists_isPullback_of_iso`: if the corner of such a square is isomorphic to
  `h M`, the square can be rewritten with an actual scheme map `M ⟶ T` as its
  side. This is the shape that `Functor.relativelyRepresentable` requires.
- `isSurjective_map` and `isOpenImmersion_map`: the image under `h` of a
  surjective map or an open immersion of schemes is surjective, respectively an
  open immersion, on all scheme tests (`MorphismProperty.relative_map`).
- `isEtale_isSurjective_of_isPullback`: a base change of `h.map p` with `p`
  étale and surjective is étale and surjective.

## Open-immersion case

`exists_iso_of_isOpenImmersion` takes a cartesian square
`IsPullback c (h.map j) φ (h.map p)` with `F` an fppf sheaf, `p : W ⟶ T`
étale and surjective, and `j` an open immersion. It proves that `F` is
represented. Let `O ⊆ T` be the open image of `j ≫ p`; it is open because
étale maps are universally open. Let `M` be `O` over `S`, and let
`q : Z ⟶ M` be the factorisation of `j ≫ p`
(`IsOpenImmersion.lift`). Then `q` is étale (`Etale.of_comp`) and surjective
onto `O`. For points `w₁ w₂ : T' ⟶ Z`, the identity `c w₁ = c w₂` holds if and
only if `w₁ ≫ q = w₂ ≫ q`:

- Forward: apply `φ`, then cancel the monomorphism `O.ι`.
- Reverse: the pair `(c w₁, w₂ ≫ j)` lifts to a point `z` of `Z` with
  `c z = c w₁` and `z ≫ j = w₂ ≫ j`, and `j` is a monomorphism, so `z = w₂`.

Both `c` (étale surjective) and `h.map q` (flat, locally finitely presented and
surjective) are fppf-locally surjective. The Library criterion
`exists_iso_of_locallySurjective_of_same_kernel` then gives `h M ≅ F`.

## Affine case

- `exists_affine_refinement`: an étale surjective `p : W ⟶ T` with `T` affine
  is refined by an étale `J : W' ⟶ W` from an affine scheme with `J ≫ p`
  surjective. The proof takes finitely many affine opens of `W` whose open
  images cover the quasi-compact `T`, and their coproduct
  (`IsZariskiLocalAtSource.sigmaDesc`). It follows the Library proof of
  `exists_affine_atlas`.
- `exists_iso_of_isAffine`: suppose the square
  `IsPullback c (h.map j) φ (h.map p)` has `p` étale and surjective, and `Z`,
  `W`, `T` affine. Then `F` is represented. `c` is étale, so it has a
  represented kernel pair `(t, s)` (`exists_kernelPair`), which gives the étale
  equivalence relation `ofKernelPair t s c`. Pasting the kernel-pair square with
  the given square shows that `IsPullback (t ≫ j) s p (j ≫ p)` holds for schemes.
  Then `hasAffineQuotient_of_isPullback_kernelPair` gives an affine quotient,
  and `exists_isAffine_iso_of_hasAffineQuotient` gives `h M ≅ F`.

## Zariski gluing over the test

`exists_iso_of_affine_pullbacks` concerns `φ : F ⟶ h T` with `F` an fppf
sheaf. Suppose that every fppf-sheaf pullback of `φ` along `h.map ι` is
represented, for each `ι : T' ⟶ T` with `T'` affine. Then `F` is represented.
Take the affine open cover `𝒰` of `T.left` and the pullbacks `Gₖ` of `φ` along
the cover maps `ιₖ`, with representations `eₖ : h Mₖ ≅ Gₖ`. The charts
`eₖ.hom ≫ ψ₁ₖ : h Mₖ ⟶ F` are open immersions, as base changes of
`h.map ιₖ`. Their coproduct map is fppf-locally surjective, by the following
argument. A section `x` of `F` over `T'` becomes, on the pullback of the Zariski
covering sieve of `𝒰` along `φ(x)`, a section whose image factors through some
`ιₖ`. It therefore lifts to `Gₖ` and then to `h Mₖ`. The Library theorem
`openChartGluing` concludes.

## The atlas square

- `exists_local_isPullback`: let `W` be a scheme with maps `p : W ⟶ T` and
  `w : W ⟶ V` that agree in `Y`. The scheme pullback `pullback q w`, with a
  canonical map `c` to `F`, forms a cartesian square
  `IsPullback c (h.map (pullback.snd q w)) φ₂ (h.map p)`. The proof pastes the
  scheme pullback square with `hsq` and uses `IsPullback.of_right`.
- `exists_iso_of_isAffine_test`: for an affine test `T` and an affine morphism
  `q`, `F` is represented. Pull the atlas back to `T`; this gives an étale
  surjective `p`, which is refined by `exists_affine_refinement`. Next,
  `exists_local_isPullback` applies. Then `pullback q (J ≫ w)` is affine,
  because its projection is a base change of `q` (`isAffine_of_isAffineHom`).
  Finally `exists_iso_of_isAffine` applies.
- `exists_iso_of_isAffineHom`: for any test `T` and an affine morphism `q`, `F`
  is represented. Combine `exists_iso_of_affine_pullbacks` with the previous
  lemma, using the pasted square
  `IsPullback (ψ₁ ≫ φ₁) ψ₂ (hom f) (h.map ι ≫ g)`.
- `exists_iso_of_isOpenImmersion_test`: for any test and an open immersion
  `q`, `F` is represented. Pull the atlas back to `T`, apply
  `exists_local_isPullback`, and note that `pullback.snd q w` is an open
  immersion by base change. Then the open-immersion case applies, with no
  affine reduction.
- `isRepresentableMorphism_of_pullbacks`: `hom f` is representable by schemes
  once every fppf-sheaf pullback along a scheme test is represented.

## Provenance

These are internal lemmas that formalise the representability part of the
proofs of Stacks Project, *Morphisms of Algebraic Spaces*, Lemmas 12.1
(Tag 03M4), 20.3 (Tag 03WG) and 45.3 (Tag 03ZQ). The cited statement Markdown
records the source `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`.

The proof route here differs from the source. Affine representability is
obtained from the Library's affine quotient of an étale equivalence relation
with a cartesian map to a kernel pair, and then glued over affine opens of the
test. Open immersions are handled directly through their open image.
