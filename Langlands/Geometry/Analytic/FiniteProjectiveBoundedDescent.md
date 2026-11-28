# Bounded descent along finite faithfully flat affinoid maps over every field

This module proves unique descent of bounded algebra maps along a finite
Banach, faithfully flat map `f : A → B` of presented affinoid algebras over a
complete ultrametric normed field `K`. The valuation of `K` may be trivial.
It also proves the localized form of this result for small affinoid spectra.
The norm estimate comes from a bounded `A`-linear retraction `r : B → A`.

## `exists_linearMap_apply_one_eq_one`

Let `B` be a commutative `A`-algebra that is faithfully flat and projective as
an `A`-module. Then there is an `A`-linear map `r : B → A` with `r 1 = 1`.

Proof. Let `J ⊆ A` be the ideal of values `r 1` for `A`-linear maps
`r : B → A`. A dual basis of the projective module `B` (`Module.projective_def`)
writes `1 = ∑ sₚ(1) bₚ` with `A`-linear coordinate maps `sₚ`, so `1 ∈ J • B`.
If `J` were proper, faithful flatness would give `J • B ≠ B`
(`Module.FaithfullyFlat.iff_flat_and_proper_ideal`). Hence `J = A`, and
`1 = r 1` for some `r`.

## `exists_norm_linearMap_le`

Let `f : A → B` be a finite Banach bounded algebra map of normed `K`-algebras
whose algebra structure `A → B` is `f`. Then every `A`-linear map
`r : B → A` satisfies `‖r y‖ ≤ M ‖y‖` for some `M ≥ 0`.

Proof. Finite Banach gives finitely many `bᵢ ∈ B` and a constant `C` such that
every `y` is `∑ f(cᵢ) bᵢ` with `‖c‖ ≤ C ‖y‖`. Then `r y = ∑ cᵢ r(bᵢ)`, so one
can take `M = C ∑ ‖r(bᵢ)‖`.

## `exists_unique_boundedDescent`

Let `f : A → B` be a finite Banach, faithfully flat bounded map of presented
affinoid algebras over `K`, and let `g : C → B` be a bounded map whose two
composites `leftMap f f ∘ g` and `rightMap f f ∘ g` into the completed
self-pushout `AffinoidPushout.algebra f f` agree. Then there is a unique
bounded `h : C → A` with `f ∘ h = g`.

Proof. Affinoid algebras are Noetherian over every field (module
`GeneralizedAffinoid.Noetherian`). Hence the finite algebra `B` is finitely
presented over `A`, and the flat, finitely presented module `B` is
projective. The first lemma gives an `A`-linear `r : B → A` with `r 1 = 1`.
The second makes `r` bounded, with constant `M`. Since `r (f a) = a`, the map
`f` is injective, and `‖a‖ ≤ M ‖f a‖`.

The range of `f` is the equalizer of the two pushout maps. The ordinary
tensor product `B ⊗_A B` maps bijectively onto the completed pushout
(`finiteTensorComparison`). An element `b` with equal images therefore
satisfies `b ⊗ 1 = 1 ⊗ b`, and faithful flatness puts `b` in the image of `A`.
This is the private lemma `mem_range_algebraMap_of_tensor_eq'`, a copy of
the private lemma of `FiniteFaithfullyFlatBoundedDescent`.

So `g` lands in the range of `f`, and `h = f⁻¹ ∘ g` is an algebra map. It is
bounded because `‖h c‖ = ‖r (g c)‖ ≤ M ‖g c‖`. Uniqueness follows from the
injectivity of `f`.

## `SmallAffinoidSpectrum.exists_unique_localizedHomDescent`

Let `f : A → B` be a finite Banach, flat map of presented affinoid algebras
that is surjective on Banach spectra, and let `C` be a presented affinoid
algebra. All three spectra are `v`-small. Let
`g : M(B) ⟶ M(C)` be a map in the localized category between the small
saturated spectra (`localizationFunctor.obj (saturated B)` and so on) whose
composites with the two projections `finitePushoutFst f f` and
`finitePushoutSnd f f` from the small spectrum of the self-pushout agree. Then
there is a unique localized `h : M(A) ⟶ M(C)` with `M(f) ≫ h = g`, where
`M(f) = localizationFunctor.map (map f)`.

Proof. `faithfullyFlat_of_flat_of_spectrum_surjective` (module
`FiniteAffinoidLocalizedHomDescent`) makes `f` faithfully flat. The bijection
`localizedMapEquiv` between bounded algebra maps and localized maps of small
affinoid spectra (module `SmallAffinoidLocalizedMaps`) is compatible with
composition (`localizedMapEquiv_comp`). It turns `g` and the matching
condition into a bounded map `g₀ : C → B` with equal composites into the
self-pushout, and the previous theorem applies to `g₀`. Uniqueness is
transported back through the same bijection.

The affinoid case in the proof of Berkovich’s Proposition 4.1.3 on printed
page 83 uses the exactness and admissibility of `0 → A → B → B ⊗_A B`.
The bounded retraction gives the admissibility estimate `‖a‖ ≤ M ‖f a‖`
over every complete ultrametric normed field.
[Berkovich, *Étale cohomology for non-Archimedean analytic spaces*](https://www.numdam.org/item/PMIHES_1993__78__5_0/)
