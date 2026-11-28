# Descent along finite étale affinoid covers into good targets

`Langlands.Analytic.SaturatedAtlasPresentation.FiniteEtaleAffinoidHomDescentGoodTargetStatement`
is a proposition about analytic morphisms over any complete ultrametric
normed field `K : Type u`, with instances `NormedField K`, `IsUltrametricDist K`
and `CompleteSpace K`. This includes fields with trivial norm. The universe `v`
used for the small spectra, spaces and chart indices is independent of `u`.

Let `A` and `B` be presented affinoid `K`-algebras with `v`-small Banach
spectra, as expressed by `Small.{v} (BanachSpectrum A)` and
`Small.{v} (BanachSpectrum B)`. A bounded algebra map `f : BoundedAlgHom K A B`
satisfies the following hypotheses.

- `f.IsFiniteBanach` gives a bounded finite free coefficient map onto `B`
  with norm-controlled preimages.
- `f.AlgebraicallyFiniteEtale` says that the underlying ring map is finite
  and étale.
- `Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)` says that
  the induced map on Banach spectra is surjective.

Write `M(A)` for `localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} A)`
and define `M(B)` likewise. The map `M(f) : M(B) ⟶ M(A)` is
`localizationFunctor.map (SmallAffinoidSpectrum.map f)`.

Let `T : SaturatedAtlasPresentation.{u, v, v} K`. Assume each point of its
underlying space has a chart whose range belongs to its neighbourhood filter,
as expressed by `∀ t : T.presentation.space, ∃ e : T.presentation.atlas.Index,
Set.range (T.presentation.atlas.chart e) ∈ 𝓝 t`. This gives a chart witness to
goodness, the existence of an affinoid neighbourhood at every point. Write
`L(T) = localizationFunctor.obj T`. If `g : M(B) ⟶ L(T)` satisfies

```text
∀ (Z : LocalizedCategory.{u, v, v} (K := K)) (a b : Z ⟶ M(B)),
  a ≫ M(f) = b ≫ M(f) → a ≫ g = b ≫ g
```

then there exists `h : M(A) ⟶ L(T)` with `M(f) ≫ h = g`.

This is the existence part of the affinoid-base test in Berkovich's
Lemma 4.1.1(2) and Proposition 4.1.3, specialized to finite étale covers
and absolute good targets. Take the ground-field analytic space \(M(K)\) as
the base and use the represented presheaf \(Y \mapsto \operatorname{Hom}(Y,T)\).
The finite Banach hypothesis gives finiteness in the affinoid category.
A finite étale ring map is flat, and spectrum surjectivity gives faithful flatness by
`SmallAffinoidSpectrum.faithfullyFlat_of_flat_of_spectrum_surjective`.
The all-test-morphism hypothesis implies agreement on the two kernel-pair
projections by applying it to those projections. Conversely, any pair of
test morphisms identified by `M(f)` factors through the kernel pair by the
pullback property. The Library supplies this pullback by
`SmallAffinoidSpectrum.exists_finite_localized_isPullback` using `finiteBanachPushout`
and `f.IsFiniteBanach`. Exactness at the middle Hom set in Lemma 4.1.1(2),
as established for good targets by Proposition 4.1.3, gives the factorization.

Source. Vladimir G. Berkovich, *Étale cohomology for non-Archimedean analytic
spaces*, Publ. Math. IHÉS 78 (1993), §1.2 (printed p. 14 for the ground field
and p. 22 for goodness), Lemma 4.1.1(2)
(printed p. 82), and Proposition 4.1.3 (printed pp. 83–84).
Literature ID `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
