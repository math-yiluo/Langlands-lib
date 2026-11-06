# Reduction of fibre power section lifting to a local base

This module reduces the published proposition
`ProperFibrePowerSectionLiftingStatement` to its case over the spectrum of a
noetherian local ring. The main result is

```
theorem properFibrePowerSectionLifting_of_local
    (h : LocalClosedFibrePowerSectionLifting.{u}) :
    ProperFibrePowerSectionLiftingStatement.{u}
```

It assumes the local case as the hypothesis `h` and does not prove it.

## The local case

`LocalClosedFibrePowerSectionLifting` is a `Prop`. It says the following. Let
`A` be a noetherian local ring with maximal ideal `𝔪`, let `f : X → Spec A` be
proper, and let `L` be a line bundle on `X`. Let `i : Z → X` and
`g : Z → Spec (A/𝔪)` be any morphisms that form a pullback square (`IsPullback`)
with `f` and `Spec (A → A/𝔪)`. If the pullback of `L` along `i` is ample, then
there is `n₀` such that for all `n ≥ n₀` the section pullback map

```
sectionPullback i (tensorPow L.obj n) ⊤ : Γ(X, L^{⊗n}) → Γ(Z, i^*(L^{⊗n}))
```

is surjective. The codomain is the actual module pullback of the tensor power.
Any base change of the closed point may serve as `Z`, so the closed-fibre
results of `IdealAdicClosedFibre` (`closedFibreIso`,
`isPullback_fiberι_closedPoint`) apply to it with `I = 𝔪`.

This is the case `F = 𝒪_X`, `Y = Spec A`, `y` the closed point, of the
surjectivity in Stacks Lemma 30.21.3 (tag 02OF). Over a local base,
`f_*(L^{⊗d})_y` equals `Γ(X, L^{⊗d})`, because the only open neighbourhood of
the closed point is the whole space.

## The reduction

Fix `s ∈ S` and an affine open `U ∋ s`. In namespace `LocalReduction`:

- `chart f hU` is the base change of `f` along `hU.fromSpec : Spec Γ(S, U) → S`.
  `localBase f hU s hs` is the further base change along
  `Spec 𝒪_{S,s} → Spec Γ(S, U)`, the `Spec` of the germ map. The projections
  are `chartToX`, `chartHom`, `localToChart`, `localToX` (to `X`) and
  `localHom` (to `Spec 𝒪_{S,s}`). `isPullback_local` states that the pasted
  square over `Spec 𝒪_{S,s} → S` is a pullback, and the instance states that
  `localHom` is proper.
- `fibreToLocal` maps the actual fibre `f.fiber s` into `localBase`.
  `isPullback_fibreToLocal` states that it is the base change of
  `Spec κ(s) → Spec 𝒪_{S,s}`, using `fromSpecResidueField_eq` and
  `IsPullback.of_right`. `isPullback_fibreToLocal_quotient` restates this
  with `κ(s)` written as `𝒪_{S,s}/𝔪`, the form used by the local case.
- `localToX_comp` and `top_le_localToX_preimage`: `localBase` lies over the
  image of `Spec 𝒪_{S,s} → S`, whose points all specialize to `s`. So every
  point of `localBase` maps into `f⁻¹V` for every open `V ∋ s`.
- `appLE_congr_hom` and `appLE_eq_germ_comp_structureRingHom`: the ring map
  `Γ(S, U) → Γ(T, ⊤)` of a scheme `T` over `Spec 𝒪_{S,s}` is the germ map
  followed by `structureRingHom`.

### Descent of sections (section `Descent`, `f` quasi-compact and quasi-separated)

`exists_sectionPullbackLE_eq` states the following. Let `M` be a line bundle
on `X`. Every global section `y` of its pullback to `localBase` is the pullback
of some section `τ` of `M` over `f⁻¹V`, for some affine open `V ∋ s`. The
proof:

1. `localToChart` is affine, and `chart` is quasi-compact and
   quasi-separated (the instances).
2. `Spec 𝒪_{S,s} → Spec Γ(S, U)` is flat, since it is a localization at the
   prime complement `P`. The Library theorem
   `CechResolution.isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs` makes
   the sections base-change map an isomorphism for the pulled-back line
   bundle on `chart`. `DerivedSections.isLocalizedModule_sectionsBaseChangeMap`
   shows that the base-change map is a localization at `P`. So `a • y` is the
   pullback of a section `m` over `chart`, for some `a ∉ 𝔭_s`.
3. `chartToX` is an open immersion with range `f⁻¹U`
   (`preimage_le_chartToX_opensRange`, `chartToX_preimage`). Then
   `sectionPullbackLE_bijective_of_isOpenImmersion` descends `m` to a section
   `t₀` of `M` over `f⁻¹U`.
4. Take `V = D(a) ⊆ U`, which contains `s` and is affine. The image of `a` is
   a unit on `f⁻¹V`. `localToX_appLE_app_map` identifies its pullback with the
   image of the germ of `a`. So `τ = a⁻¹ · t₀|_{f⁻¹V}` pulls back to `y`.

### Transport of the fibre section

- `inv_app_hom_app`, `hom_app_inv_app`, `natIso_hom_app_inv_app` and
  `pullback_map_inv_app_map_hom_app` cancel isomorphisms on sections.
- `sectionPullbackLE_naturality`: section pullback commutes with morphisms of
  modules.
- `isAmple_fibreToLocal`: if `L` is ample on the fibre, then so is the
  pullback of `L|_{localBase}` along `fibreToLocal`. This is `IsAmple.of_iso`
  with the composition and congruence isomorphisms of module pullback.
- `fibreSectionTransport` sends a section `σ` of `(fiberι s)^*(L^{⊗n})` to a
  section of `fibreToLocal^*((L|_{localBase})^{⊗n})`. It uses the
  `pullbackCongr`, `pullbackComp` and `actualPullbackTensorPowIso`
  isomorphisms.
- `sectionPullbackLE_eq_of_lift` is stated for arbitrary morphisms
  `i : Z → Y`, `p : Y → W`, `q : Z → W` with `i ≫ p = q`, a module `M` on `W`,
  and an isomorphism `Φ : p^*M ≅ N`. Suppose `y ∈ Γ(N, ⊤)` pulls back along
  `i` to the transport of `σ ∈ Γ(q^*M, ⊤)`, and `τ` pulls back along `p` to
  `Φ⁻¹ y`. Then `τ` pulls back along `q` to `σ`. The proof rewrites with
  `pullbackCongr_hom_sectionPullbackLE`, `pullbackComp_hom_sectionPullbackLE`
  and naturality, then cancels the isomorphisms. It is stated generically so
  that the kernel does not have to unfold the concrete pullback schemes; a
  version specialized to them hit a kernel deterministic timeout.
- `fibreNeighbourhoodSection_eq_of_lift` specializes it to
  `i = fibreToLocal`, `p = localToX`, `q = f.fiberι s` and
  `M = L^{⊗n}`. Its conclusion is
  `fibreNeighbourhoodSection f s (L^{⊗n}) hsV τ = σ`.

### Proof of `properFibrePowerSectionLifting_of_local`

Given `X`, `S` locally noetherian, `f` proper, `L`, and `s` with `L` ample on
the fibre `f.fiber s`:

1. Choose an affine open `U ∋ s` (`isBasis_affineOpens`).
2. Apply `h` to `A = 𝒪_{S,s}`, which is noetherian and local, with
   `localHom` (proper), `L|_{localBase}`, `Z = f.fiber s` and `i = fibreToLocal`.
   The pullback square is `isPullback_fibreToLocal_quotient` and ampleness is
   `isAmple_fibreToLocal`. This gives `n₀`.
3. For `n ≥ n₀` and a fibre section `σ`, surjectivity gives `y` lifting
   `fibreSectionTransport σ`. Then `exists_sectionPullbackLE_eq`, applied to
   `M = L^{⊗n}` and `Φ⁻¹ y`, gives `V`, `τ`.
4. `fibreNeighbourhoodSection_eq_of_lift` shows `τ` restricts to `σ`.

All universes, possibly non-reduced schemes and the specified line bundle are
kept. No flatness of `f` and no ampleness over a neighbourhood are assumed.

## Provenance

This follows the first paragraph of the proof of Stacks Lemma 30.21.3
(tag 02OF): base change to `Spec 𝒪_{Y,y}`, which is flat, identifies the
fibres, so one may assume `Y` is the spectrum of a noetherian local ring. The
Stacks proof transports cohomology along the flat base change (Lemma 30.5.2).
Here only `H⁰` of line bundles is needed. Flat base change of sections for
quasi-compact quasi-separated morphisms is combined with descent from the
localization to an affine basic open neighbourhood, which is needed because the
target statement asks for a section over `f⁻¹V` for an affine `V ∋ s`.
`LocalClosedFibrePowerSectionLifting` is an internal intermediate proposition
derived from that lemma's local case; its proof is not part of this module.
The proofs are internal, from Mathlib's scheme pullbacks, module pullback and
adjunction, and the Library modules `QCQSLineBundleSectionsBaseChange`,
`LocalizationSectionsBaseChange`, `PullbackAffineSections`,
`FibreNeighbourhoodSections`, `AmpleIsoProof` (`IsAmple.of_iso`) and
`ClosedImmersionPullbackAmpleProof` (`actualPullbackTensorPowIso`).
