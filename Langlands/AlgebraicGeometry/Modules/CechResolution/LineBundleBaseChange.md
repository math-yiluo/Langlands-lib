# Canonical scalar flat base change for actual line bundles

This internal construction specializes the actual Čech comparison to locally
free rank-one line bundles. All schemes and rings lie in an arbitrary common
universe `u`.

`isZero_higherDirectImage_pullback_lineBundle` proves that for every affine
morphism `g : Y ⟶ X`, every actual line bundle `L` on `X`, and every `q : ℕ`,
the higher direct image `R^(q+1) g_* (g^* L)` is zero. The local rank-one
pullback result makes the actual pulled-back sheaf quasi-coherent, and
`affineQuasicoherentHigherDirectImageVanishing` gives the conclusion. This
vanishing lemma requires no flatness, separation, finiteness, or base assumption.

Let `φ : R ⟶ S`, `f : X ⟶ Spec R`, `f' : Y ⟶ Spec S`, and `g : Y ⟶ X`
form a Cartesian square with specified commutativity proof `w`. Assume `g`
is affine, `f` is separated, and `φ` is flat. For an ordered affine cover `𝒰`
of `X`, `isIso_scalarBaseChangeMap_lineBundle_of_cech` proves that the actual
canonical scalar cohomology base-change map for `L.obj` is invertible in every
degree `n : ℕ`. The proof supplies all acyclicity inputs of
`isIso_scalarBaseChangeMap_of_cech`: separatedness of `f'` follows by base
change from `f`; both `L.obj` and its actual pullback are quasi-coherent;
`isZero_relativeCohomology_cechTerm` gives positive relative cohomology
vanishing for every term of both Čech complexes. The affine higher-direct-image
input is the vanishing lemma above.

`lineBundleScalarBaseChangeIsoOfCech` packages this canonical map as an
isomorphism. For a quasi-compact `X`, `isIso_scalarBaseChangeMap_lineBundle`
uses `Scheme.OrderedAffineCover.ofCompactSpace X` to supply the cover, and
`lineBundleScalarBaseChangeIso` packages the resulting comparison without an
explicit cover argument. Its type is

```lean
(ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj L.obj) ≅
  (relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj L.obj)
```

The forward morphism of each packaged isomorphism is exactly
`scalarBaseChangeMap`, with `isZero_higherDirectImage_pullback_lineBundle`
as its vanishing proof argument. Thus this construction identifies the
canonical map, rather than choosing an arbitrary isomorphism between the two
cohomology modules.

The provenance is the internal specialization and assembly of the imported
results. The implemented proof uses the sheafified Čech resolution, the
canonical comparison of acyclic resolutions with derived functors, and affine
sections base change. It imposes no noetherian or reducedness restriction and
needs no cohomology vanishing hypotheses from its caller. This pair does
not establish derived scalar base change or relative cube detection.
