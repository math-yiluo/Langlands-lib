# Killing cohomology classes by powers of a section

This module proves `twistKilling : TwistKillingStatement`, the statement of module
`SerreVanishing.Iterate`. For a proper scheme `X` over a field `K`, a locally free rank-one
`N`, a global section `s` with `trivializationOpen N s` affine, and a quasi-coherent `Z`,
every class `ξ ∈ H^{p+1}(X, Z)` is killed by `twistPow N s k` for some `k`. Here `H^n` is
`(DerivedSections.relativeGlobalSections f).rightDerived n`, the Library's
`relativeCohomology f n`. `twistPow N s k : Z ⟶ (twistIter N k).obj Z` is multiplication
by `s ^ k`.

## Auxiliary results

- `app_cechRes`: morphisms of modules commute with the Library's restriction `Cech.res`.
- `isLocalizingAt_biproduct`: a finite biproduct `⨁ G` of modules with the localization
  property `IsLocalizingAt (G i) V` (module `QuasicoherentLocal.Basic`) has it too. The
  exponents are the sums of the exponents of the summands.
- `isAffineLocallyQuasicoherent_sheafOn` (for `f : X ⟶ Spec R` separated): for a
  quasi-coherent `M` and an affine open `W`, the sheaf of sections over `W`,
  `CechResolution.sheafOn M W`, is affine-locally quasi-coherent. This is the pushforward
  along the affine morphism `W.ι`.
- `isQuasicoherent_cechTerm` (for `f` separated): the terms `CechResolution.cechTerm 𝒰 M p`
  of the Čech complex of a quasi-coherent `M` for an ordered affine cover `𝒰` are
  quasi-coherent. They are finite biproducts of such pushforwards. The intersections
  `𝒰.inter s` are affine by separatedness.
- `cechCokernelSc 𝒰 Z` is the short complex `Z ⟶ C⁰(𝒰, Z) ⟶ Q`, made of the Čech
  augmentation and its cokernel `Q`. `cechCokernelSc_shortExact` proves it short exact,
  using `CechResolution.mono_augmentation`.
- `shortExact_twistIter`: each `twistIter N k` preserves short exact sequences when
  `N` is locally free of rank one, by the Library's `shortExact_tensorBy`. The instance
  `twistIter_preservesZeroMorphisms` is used to map short complexes.
- `twistPowHom N s S k : S ⟶ S.map (twistIter N k)` is the morphism of short complexes
  with components `(twistPow N s k).app S.Xᵢ`.
- `rightDerivedZero_map_apply`: under `rightDerivedZeroIsoSelf`, `H⁰` of a morphism acts
  on elements as the morphism on global sections.

## Dimension shifting

`exists_twistPow_eq_zero_of_shortExact`: let `S : 0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be short
exact with `H^{n+1}(S.X₂) = 0`. Suppose every `η ∈ Hⁿ(S.X₃)` has some `k` such that
`Hⁿ((twistPow N s k).app S.X₃) η` lies in the image of `Hⁿ((twistIter N k).map S.g)`.
Then every `ξ ∈ H^{n+1}(S.X₁)` is killed by some `twistPow N s k`.

Proof: `H^{n+1}(S.X₂) = 0` makes the connecting map `δ : Hⁿ(S.X₃) ⟶ H^{n+1}(S.X₁)`
surjective (`DerivedPlus.epi_rightDerivedδ_of_isZero`), so `ξ = δ η`. Choose `k` and `y`
for `η`. The twisted sequence `S.map (twistIter N k)` is short exact.

- Naturality of `δ` for `twistPowHom` (`DerivedPlus.rightDerivedδ_naturality`) gives
  `H^{n+1}(twistPow) ξ = δ' (Hⁿ(twistPow) η)`, where `δ'` is the connecting map of the
  twisted sequence.
- By the choice of `y`, the right side is `δ' (Hⁿ(g') y)`, where `g'` is the twisted
  `S.g`.
- `δ' ∘ Hⁿ(g') = 0` (`DerivedPlus.rightDerived_map_comp_δ`), so the class is zero.

## The induction

`exists_lift_twist`: assume `f` separated, `X` quasi-compact and `trivializationOpen N s`
affine. Let `π : C ⟶ Q` be an epimorphism of quasi-coherent modules and `q ∈ Γ(Q, X)`.
Then for some `m` there is `a ∈ Γ((twistIter N m).obj C, X)` with
`((twistIter N m).map π) a = (twistPow N s m) q`.

Proof: `exists_global_lift` (module `SerreVanishing.Glue`) for the systems of twists of
`C` and `Q`, with `U = trivializationOpen N s`. Its inputs are:

- the charts `twistModChart` (module `SerreVanishing.ChartOf`) around each point, which
  have coefficient `c` with `X.basicOpen c = T ⊓ U` by the Library's `basicOpen_chartCoeff`;
- `isLocalizingAt_of_isQuasicoherent` for `C` and `Q` over affine opens;
- surjectivity of `π` on affine sections (`surjective_app_of_epi`);
- affine intersections (`CechResolution.isAffineOpen_inf`);
- the families `p m = (twistPow N s m) q` and `q m = (twistPow N s m) c₀`, where
  `c₀ ∈ Γ(C, U)` lifts `q|_U` by surjectivity of `π` on the affine `U`.

`exists_twistPow_eq_zero`: for `f` separated, `X` quasi-compact, `trivializationOpen N s`
affine and an ordered affine cover `𝒰`, the following holds for every `p`. Every class in
`H^{p+1}(X, Z)` of every quasi-coherent `Z` is killed by some `twistPow N s k`.

The proof is by induction on `p`, applying dimension shifting to `cechCokernelSc 𝒰 Z`.
`C⁰(𝒰, Z)` has vanishing higher cohomology
(`CechResolution.isZero_relativeCohomology_cechTerm`), and `C⁰(𝒰, Z)` and `Q` are
quasi-coherent (`isQuasicoherent_cechTerm`, `isQuasicoherent_cokernel`).

- `p = 0`: identify `H⁰` with global sections by `rightDerivedZeroIsoSelf`. The image
  condition is `exists_lift_twist` for `π = cokernel.π`.
- `p + 1`: by the induction hypothesis applied to `Q`, the class `Hⁿ(twistPow) η` is zero,
  so it is the image of `0`.

`twistKilling` derives the hypotheses from properness. `f` is separated, and `X` is
quasi-compact since `f` is quasi-compact over the affine `Spec K`
(`QuasiCompact.compactSpace_of_compactSpace`). An ordered affine cover comes from
`BiCech.exists_frameCover`; only its existence is used.

## Provenance

The statement is Stacks Project, Lemma 30.17.4, tag
[01XR](https://stacks.math.columbia.edu/tag/01XR), in the form recorded in module
`SerreVanishing.Iterate`. Stacks deduces it from the vanishing of quasi-coherent
cohomology on the affine `X_s` together with its previous lemma, which compares
cohomology over `X_s` with the colimit along multiplication by `s`. This proof uses the
Library's derived-functor long exact sequence instead. It shifts dimension through the
Čech short exact sequence `0 → Z → C⁰(𝒰, Z) → Q → 0`, whose middle term is acyclic for a
separated `X`. In the base case the colimit description of sections over `X_s` is used in
the lifting form of module `SerreVanishing.Glue`, after Stacks Lemma 28.18.2 (tag
[01PW](https://stacks.math.columbia.edu/tag/01PW)). This route is derived for this proof.
