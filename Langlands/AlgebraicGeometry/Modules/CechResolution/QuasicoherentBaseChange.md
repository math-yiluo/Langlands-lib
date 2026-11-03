# Canonical scalar flat base change for quasi-coherent modules

This internal generalization of `CechResolution.LineBundleBaseChange` applies
the published actual Čech comparison to every quasi-coherent coefficient
module. Its inputs are the published canonical scalar cohomology map,
acyclicity of quasi-coherent Čech terms, affine higher-direct-image
vanishing, preservation of quasi-coherence by pullback, and finite ordered
affine covers of quasi-compact schemes. It asserts no new external-source
theorem. Schemes and coefficient rings lie in an arbitrary common universe
`u`.

For an affine morphism `g : Y ⟶ X` and any quasi-coherent `M : X.Modules`,
`isZero_higherDirectImage_pullback_quasicoherent` proves
`R^(q+1) g_* (g^* M) = 0` in every positive degree. The published
`isQuasicoherent_pullback` instance makes the actual pullback
quasi-coherent, and
`affineQuasicoherentHigherDirectImageVanishing` proves the vanishing.
This lemma needs no flatness, separation or compactness hypothesis.

Let `φ : R ⟶ S`, `f : X ⟶ Spec R`, `f' : Y ⟶ Spec S`, and
`g : Y ⟶ X` form a cartesian square with specified commutativity proof
`w`. Assume `g` is affine, `f` is separated, `φ.hom` is flat, and `M`
is quasi-coherent. Given an ordered affine cover `𝒰` of `X`,
`isIso_scalarBaseChangeMap_quasicoherent_of_cech` proves invertibility
of the canonical scalar map in every degree `n : ℕ`. The proof discharges
all three acyclicity premises of
`isIso_scalarBaseChangeMap_of_cech`. Separatedness of `f'` follows
by base change. The source coefficient and its actual pullback are
quasi-coherent, so `isZero_relativeCohomology_cechTerm` proves acyclicity
of the terms of both actual Čech complexes. The affine vanishing lemma
above supplies the higher-direct-image premise.

`quasicoherentScalarBaseChangeIsoOfCech` packages that map as an
isomorphism. If `X` is quasi-compact, represented in Lean by
`[CompactSpace X]`, `isIso_scalarBaseChangeMap_quasicoherent` supplies
`Scheme.OrderedAffineCover.ofCompactSpace X`, and
`quasicoherentScalarBaseChangeIso` gives

```text
S ⊗_R H^n(X, M) ≅ H^n(Y, g^* M).
```

More precisely the source is
`(ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj M)`
and the target is
`(relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj M)`.
`quasicoherentScalarBaseChangeIso_hom` identifies its forward map with
the published `scalarBaseChangeMap` using the proved affine vanishing.
`quasicoherentScalarBaseChangeIso_one_tmul` says that this forward map
sends `1 ⊗ x` to the actual published semilinear `baseChangeMap` image
of `x`. It uses the published injective-pushforward acyclicity proof
as the remaining argument of that map.
`quasicoherentScalarBaseChangeIso_naturality` proves the commuting
square for any morphism between quasi-coherent coefficient modules by
the published naturality of `scalarBaseChangeMap`.

These constructions require no flatness of `f`, properness, noetherian
hypothesis, or finite presentation of `M`. The affine hypothesis on
`g` is retained to match the existing canonical comparison API; in
this cartesian setting it also follows because `Spec.map φ` is affine.
The result concerns ordinary nonnegative cohomology and canonical
scalar base change. It makes no claim about unit boundaries, Picard
lifting fibres, their scalar structure, or representability.
