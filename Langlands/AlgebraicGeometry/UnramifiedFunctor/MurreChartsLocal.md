# Local properties of elements of a functor, for Murre's charts

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocal`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts`. General tools for the chart
construction in `MurreCharts`. `F` is a presheaf on `Over S`. `InfinitesimallyEtaleAt` and
`IsMonoElement` are the published notions of `MurreLocalToGlobalSteps` (SGA 3, XI 1.6–1.8:
an element `ξ ∈ F(U)` viewed as a morphism `U → F`).

## Points of local artinian schemes

* `eq_of_isArtinianRing`: the spectrum of a local artinian ring has a single point (every
  prime is maximal).
* `ne_top_of_isNilpotent`, `isLocalRing_quotient`: for a nilpotent ideal `J` of a local ring
  `A`, `J ≠ ⊤` and `A ⧸ J` is local.

## Transfer of infinitesimal étaleness (section `Etale`)

* `infinitesimallyEtaleAt_of_factor`: let `ρ : V ⟶ U` in `Over S`, `ξ ∈ F(U)`, `y ∈ U`.
  Suppose that every morphism from the spectrum of a local artinian ring to `U` with image `y`
  factors uniquely through `ρ`, and that `F(ρ)(ξ)` is infinitesimally étale at every preimage
  of `y`. Then `ξ` is infinitesimally étale at `y`. Proof: factor the given `u₀`, solve the
  lifting problem on `V`, compose with `ρ`; uniqueness from the uniqueness of factorizations
  over `A` and `A/J`.
* `infinitesimallyEtaleAt_restrict`: for an open immersion `ι : V ⟶ U`, if `ξ` is
  infinitesimally étale at `ι(y)`, then `F(ι)(ξ)` is infinitesimally étale at `y`. The lift
  on `U` lands in the image of `ι` (its source has one point), so it factors through `ι`.
* `isMonoElement_restrict`: monomorphic elements restrict along monomorphisms.

## Representability over a monomorphism (section `Rep`)

Let `g : S' ⟶ S` and let `e` represent `baseChange g F` by `Y' : Over S'`.

* `liftIso`, `elemEquiv g e T t ht`: for `T : Over S` with structure morphism `t ≫ g`, the
  bijection `(Over.mk t ⟶ Y') ≃ F(T)` (the representation composed with `T ≅ Over.map g (t)`).
* `lift_comp`, `elemEquiv_naturality`: if `g` is a monomorphism, every `S`-morphism
  `h : T₁ ⟶ T₂` between such objects is an `S'`-morphism, and `elemEquiv` is natural in it.
* `infinitesimallyEtaleAt_elemEquiv`: suppose `g` is a monomorphism and every morphism from the
  spectrum of a local artinian ring to `S` with image in the image of `g` factors through `g`.
  Then for every open immersion `j : Over.mk w ⟶ Y'` the element `elemEquiv g e V w hw j` is
  infinitesimally étale at every point. The lifting problem translates, by `elemEquiv`, into
  extending `Spec(A/J) → Y'` along the given `Spec A → Y'`, which lands in the image of `j`.

## The diagonal (section `Diagonal`)

For `q : U ⟶ S'` and `h₁ h₂ : Z ⟶ U` with `h₁ ≫ q = h₂ ≫ q`:

* `eq_of_forall_mem_range_diagonal`: if the diagonal of `q` is an open immersion and
  `(h₁, h₂) : Z ⟶ U ×_{S'} U` maps every point into its image, then `h₁ = h₂`
  (factor through the diagonal).
* `lift_mem_range_diagonal`: if `k ≫ h₁ = k ≫ h₂`, then `(h₁, h₂)` maps the image of `k` into
  the image of the diagonal.
* `isOpen_preimage_range_diagonal`, `eq_of_isLocalRing`: for `Z = Spec L` with `L` local, it
  suffices that `h₁` and `h₂` agree after a morphism hitting the closed point, since every
  point specializes to the closed point and the preimage of the diagonal is open.

Mathlib provides the openness of the diagonal for formally unramified morphisms locally of
finite type (`AlgebraicGeometry.isOpenImmersion_diagonal`).

## Stalks (section `Stalk`)

* `mono_specMap_of_epi`, `mono_fromSpecStalk`: `Spec 𝒪_{Spec R, s} ⟶ Spec R` is a
  monomorphism (`Spec` is a right adjoint and `R → 𝒪_s` is a localization, hence an
  epimorphism).
* `exists_comp_fromSpecStalk`, `fromSpecStalk_factor`: a morphism from the spectrum of a local
  ring whose closed point maps to a generization of `s` factors through
  `X.fromSpecStalk s` (Mathlib's `Spec_stalkClosedPointTo_fromSpecStalk` and
  `SpecMap_stalkSpecializes_fromSpecStalk`); this is the factorization hypothesis of
  `infinitesimallyEtaleAt_elemEquiv`.
