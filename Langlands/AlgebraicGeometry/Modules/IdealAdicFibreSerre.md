# Serre vanishing for modules annihilated by a maximal ideal of the base

This derived module supplies the Serre-vanishing hypothesis `hserre` of
`exists_uniform_vanishing_adicLayer_tensorPow` (module `IdealAdicGradedFamily`)
when the ideal is maximal. It then states the resulting uniform vanishing for
the maximal-ideal layers of the powers of a line bundle over a noetherian local
base. Throughout, `f : X ⟶ Spec R` is a morphism, `I` an ideal of `R`, and
`i : Z ⟶ X`, `g : Z ⟶ Spec (R/I)` form a pullback square
`hpb : IsPullback i g f (Spec.map (quotientRingHom I))`. So `Z` is the base
change of `X` along `Spec (R/I) → Spec R`, and `i` is a closed immersion.

## Annihilated modules come from the closed fibre

- `inclusion_eq_zero_of_smulEnd`: if `smulEnd f a G = 0` for every `a ∈ I`,
  then the inclusion `IG ⟶ G` of the sheaf of `I`-multiples is zero. By the
  published `inclusion_comp_eq_zero_iff` it suffices that every section
  `scalar f U a • m` with `a ∈ I` vanishes. That section is the value of
  `smulEnd f a G` at `m`, which is zero.
- `closedFibreIsoOfAnnihilated hpb G h : G ≅ i_* i^* G` holds for
  quasi-coherent `G` with `smulEnd f a G = 0` for all `a ∈ I`. Since the
  inclusion `IG ⟶ G` is zero, the cokernel projection `G ⟶ G/IG`
  (`projection f I G`) is an isomorphism (`cokernel.π_of_zero`). The
  definition composes it with the published `closedFibreIso hpb G :
  G/IG ≅ i_* i^* G`. `closedFibreIsoOfAnnihilated_hom` records that the
  forward map is the unit of the adjunction `i^* ⊣ i_*` at `G`.
- `hasFiniteAffineSections_pullback_of_isPullback`: if a quasi-coherent `G` has
  finitely generated sections on every affine open, so does `i^* G` on `Z`.
  It suffices to check this on an affine cover
  (`HasLocallyFiniteSections.finiteAffineSections`). Every point of `Z` lies in
  some `i⁻¹ U` with `U ⊆ X` affine. Over such `U`, the published section
  pullback `Γ(G, U) → Γ(i^* G, i⁻¹ U)` is surjective
  (`sectionPullback_surjective_of_isPullback`) and semilinear over the
  surjective ring map `Γ(X, U) → Γ(Z, i⁻¹ U)`. So the image of a finite
  generating set generates.

## Serre vanishing for one annihilated module

`exists_vanishing_tensorPow_of_annihilated` assumes that `I` is maximal, `f` is
proper, `L` is a line bundle on `X` whose pullback `i^* L` is ample, and
`AnnihilatedCoherent f I G`. That is, `G` is quasi-coherent, has finitely
generated affine sections, and `I` acts on it by zero. The conclusion is a
bound `d₀` with `H^{p+1}(X, G ⊗ L^d) = 0` for all `d ≥ d₀` and all `p`.
Cohomology is the relative cohomology over `f`. The proof has four steps.

1. `R/I` is a field and `g` is proper, as a base change of `f`
   (`MorphismProperty.of_isPullback`). The published
   `properAmplePairSerreVanishing` applies to `K = i^* G` with
   `L₁ = L₂ = i^* L`. It gives `n₀` with
   `H^{q}(Z, (K ⊗ (i^*L)^a) ⊗ (i^*L)^b) = 0` for `a, b ≥ n₀` and `q > 0`.
2. Take `d₀ = n₀ + n₀`. Write `d = n₀ + b` with `b ≥ n₀` and use `a = n₀`.
   Associativity and `tensorPowAddIso` identify the module in step 1 with
   `K ⊗ (i^*L)^d`. `isZero_relativeCohomology_iff` moves the vanishing from
   relative cohomology over `g` to relative cohomology over `i ≫ f`.
3. `i` is a closed immersion, so its higher direct images vanish
   (`closedImmersionHigherDirectImageVanishing`), and `pushforwardCohomologyIso`
   identifies `H^{p+1}` over `i ≫ f` with `H^{p+1}(X, i_*(K ⊗ (i^*L)^d))` over
   `f`.
4. The projection formula `coherentTwistPushforwardIso i K L d :
   (i_* K) ⊗ L^d ≅ i_*(K ⊗ (i^*L)^d)`, together with
   `closedFibreIsoOfAnnihilated` twisted by `L^d`, identifies the last module
   with `G ⊗ L^d`.

## Uniform vanishing over a noetherian local base

`exists_uniform_vanishing_adicLayer_maximalIdeal` assumes that `R` is a
noetherian local ring with maximal ideal `𝔪` and that `f` is proper. Here `i`
and `g` form a pullback square over `Spec (R/𝔪) → Spec R`, and `i^* L` is
ample on the closed fibre `Z`. Then one `d₀` gives
`H^{p+1}(X, 𝔪ⁿL^d / 𝔪ⁿ⁺¹L^d) = 0` for all `d ≥ d₀` and all `n`, `p`. The
layers are `adicLayer f 𝔪 (tensorPow L.obj d) n`. `X` is noetherian: it is
locally noetherian (`LocallyOfFiniteType.isLocallyNoetherian`) and compact,
because `f` is quasi-compact over the compact space `Spec R`. The theorem
applies the published `exists_uniform_vanishing_adicLayer_tensorPow` with
`J = 𝔪`, which is finitely generated because `R` is noetherian. The hypothesis
`hserre` is `exists_vanishing_tensorPow_of_annihilated`.

## Provenance

The last theorem is the uniform vanishing statement in the proof of Stacks
Project Lemma 30.21.3 (registered snapshot
`stacks-noetherian-fibre-section-lifting-2026-11-03`, `02OF.txt`), for
`F = O_X`. There `H^p(X, 𝔪ⁿO_X / 𝔪ⁿ⁺¹O_X ⊗ L^d)` vanishes for all `n ≥ 0`,
all `p > 0` and all `d ≥ d₀`. The Lean statement uses the layers
`𝔪ⁿL^d / 𝔪ⁿ⁺¹L^d` of the powers themselves, which the published
`layerTwistIso` identifies with these twists. The Stacks proof regards all
layers as coherent modules on the closed fibre (Lemma 30.9.8). It assembles
them into one graded module of finite type over `f_y^* Gr_𝔪(A)` and applies
graded Serre vanishing (Lemma 30.19.3) and then Lemma 30.2.4. Here the
published devissage of `IdealAdicGradedFamily` instead reduces the claim to
single coherent modules annihilated by `𝔪`. Each such module is pushed forward
from the closed fibre, where the published Serre vanishing over a field
applies. The lemmas in this module are internal steps of that argument.
