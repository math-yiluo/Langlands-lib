# The local closed-fibre case from stable images and layer vanishing

This module proves the closed-fibre case over a noetherian local base,
`LocalClosedFibrePowerSectionLifting` from
`ProperFibrePowerSectionLiftingLocalReduction`, from two hypotheses:

```
theorem localClosedFibrePowerSectionLifting_of_layerVanishing
    (hs : ProperAdicCohomologyStableImageStatement.{u})
    (hv : LocalAdicLayerVanishing.{u}) :
    LocalClosedFibrePowerSectionLifting.{u}
```

Both hypotheses are taken as assumptions and are not proved here.
`ProperAdicCohomologyStableImageStatement` is the published statement of
Stacks Lemma 30.20.4(3). `LocalAdicLayerVanishing` is the new proposition below.

## The layer vanishing proposition

`LocalAdicLayerVanishing` uses the same setting as the local case. `A` is a
noetherian local ring with maximal ideal `𝔪`, `f : X → Spec A` is proper, `L`
is a line bundle on `X`, and `i : Z → X`, `g : Z → Spec (A/𝔪)` form a pullback
square (`IsPullback`) with `f` and `Spec (A → A/𝔪)`. If the pullback of `L`
along `i` is ample, the proposition gives an `n₀` with the following property.
For every `n ≥ n₀` and every `k ≥ 0`, the first relative cohomology
`H¹(X, 𝔪^k L^{⊗n} / 𝔪^{k+1} L^{⊗n})` vanishes, as a zero object of `A`-modules.
The layer is the published `IdealAdic.adicLayer f 𝔪 (tensorPow L.obj n) k`: the
cokernel of the canonical map between the actual sheaves of local ideal
multiples. The cohomology is `DerivedSections.relativeCohomology f 1`.

This is the case `F = 𝒪_X`, `p = 1` of the vanishing in the proof of Stacks
Lemma 30.21.3 (tag 02OF):
`H^p(X, 𝔪^n F/𝔪^{n+1} F ⊗ L^{⊗d}) = 0` for all `p > 0`, `d ≥ d₀` and `n ≥ 0`.
The source deduces it from Lemma 30.19.3(2) on the closed fibre. The
proposition records only the degree `p = 1` that the argument here uses. For
`F = 𝒪_X` it uses the layer of `L^{⊗n}` itself, which is isomorphic to the
twisted layer `(𝔪^k 𝒪_X/𝔪^{k+1} 𝒪_X) ⊗ L^{⊗n}` of the source.

## Declarations

- `LocalCase.surjective_map_iff_of_iso`: for a natural isomorphism `e : F ≅ G`
  of functors to `R`-modules, `F.map φ` is surjective iff `G.map φ` is.
- `LocalCase.surjective_sectionPullback_of_isZero_layer`: let `R` be noetherian,
  `I` an ideal, `f : X → Spec R` proper, and `i : Z → X`, `g : Z → Spec (R/I)` a
  pullback square over `Spec (R → R/I)`. Let `M` be quasi-coherent with finitely
  generated sections on affine opens (`HasFiniteAffineSections`). Assume
  `H¹(I^k M / I^{k+1} M) = 0` for every `k`. Then, given the stable-image
  statement, `sectionPullback i M ⊤ : Γ(X, M) → Γ(Z, i^*M)` is surjective.
  The proof:
  1. The stable-image statement in degree `0` gives `c` such that the image
     of `H⁰(M/I^{1+c} M) → H⁰(M/I M)` equals the image of `H⁰(M) → H⁰(M/I M)`.
  2. The published lemma `IdealAdic.surjective_sections_adicTransition` uses
     the layer vanishing to make the transition
     `Γ(M/I^{1+c} M) → Γ(M/I M)` surjective. `relativeCohomologyZeroIso`
     carries this to `H⁰`, so `H⁰(M) → H⁰(M/I M)` is surjective, and then so
     is the section map of the projection `M → M/I M` over `X`. The ideal
     `I^1` is replaced by `I` by generalizing over an ideal equal to `I`.
  3. `IdealAdic.closedFibreIso` identifies `M/I M` with `i_* i^* M`, and
     `projection_closedFibreIso_hom` states that the projection followed by
     it is the pullback-pushforward unit. The section map of that unit over
     `⊤` is `sectionPullback i M ⊤`. Composing with the isomorphism gives the
     surjectivity.
- `localClosedFibrePowerSectionLifting_of_layerVanishing`: apply `hv` to obtain
  `n₀`. For `n ≥ n₀`, apply the previous lemma to `R = A`, `I = 𝔪` and
  `M = L^{⊗n}`. `M` is locally free of rank one
  (`tensorPow_isLocallyFreeRankOne`), so it is quasi-coherent
  (`IsLocallyFreeRankOne.isQuasicoherent`) and has finite affine sections
  (`IsLocallyFreeRankOne.isFinitePresentation`,
  `hasFiniteAffineSections_of_isFinitePresentation`).

All universes, possibly non-reduced schemes and the specified line bundle are
kept, and no flatness is assumed.

## Provenance

The argument is the last step of the proof of Stacks Lemma 30.21.3 (tag 02OF),
for `F = 𝒪_X` and `p = 0`. Induction on the layer sequences makes the maps
`H⁰(X, F/𝔪^n F ⊗ L^{⊗d}) → H⁰(X_y, F_y ⊗ L_y^{⊗d})` surjective, and
Lemma 30.20.4(3) then gives surjectivity from `H⁰(X, F ⊗ L^{⊗d})`. Here
`X_y` is any base change `Z` of the closed point, identified with the closed
subscheme cut out by `𝔪` through the published `closedFibreIso`.
`LocalAdicLayerVanishing` is an internal intermediate proposition, derived
from the vanishing statement in that proof.
