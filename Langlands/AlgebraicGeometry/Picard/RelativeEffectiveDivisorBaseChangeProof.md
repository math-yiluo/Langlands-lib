# Arbitrary base change of relative effective Cartier divisors (proof)

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof` proves

```lean
theorem relativeEffectiveDivisorBaseChange :
    RelativeEffectiveDivisorBaseChangeStatement.{u}
```

(namespace `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof`).

Notation: `f : X ⟶ S`; `I` is an actual ideal with closed immersion `i = I.subschemeι : E ⟶ X`;
`K = kernelModule i` is its ideal module, with inclusion `ι = kernelModuleι i : K ⟶ 𝒪_X`;
`π = unitToPushforwardUnit i : 𝒪_X ⟶ i_* 𝒪_E` is the structure map. The hypothesis is that `K`
is locally free of rank one and that `i ≫ f` is flat. For `g : T ⟶ S`, `p = pullback.snd g f`.

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1 (2005), p.23,
Definition 3.6 and the paragraph after it (literature id
`kleiman-2005-picard-scheme-arxiv-math0504020v1`). That paragraph uses flatness of the divisor
over the base to show that the pulled-back ideal is the ideal of the base change. The Lean proof
follows this argument for arbitrary schemes, as follows.

## Proof

1. **The structure map is an epimorphism** (`epi_unitToPushforwardUnit`). For a closed
   immersion `i`, `π` is surjective on sections over every affine open
   (`Scheme.Hom.app_surjective`). Affine opens form a basis, so `π` is locally surjective, and
   the underlying sheaf map is an epimorphism (`TopCat.Sheaf.isLocallySurjective_iff_epi`).
   Hence `π` is an epimorphism of modules.
2. **Transport of the ideal module** (section `KernelBaseChange`). Take a cartesian square
   `IsPullback p' i' i b` with `i` a closed immersion, and suppose `b^*(ι)` is a monomorphism.
   Then `b^*(ι)` is a kernel of `b^*(π)` (`pullbackKernelIsKernel`). The reason is that
   `0 → K → 𝒪_X → i_*𝒪_E` is exact with `π` epi, and `b^*`, as a left adjoint, preserves
   cokernels (`ShortComplex.Exact.map_of_epi_of_preservesCokernel`, then `fIsKernel`). The
   Library's `structureMap_baseChange` identifies `b^*(π)` with the structure map of `i'`, up to
   `pullbackUnitIso` and `structurePushforwardBaseChangeIso`. Comparing kernels then gives
   `kernelModuleBaseChangeIso : b^* K ≅ kernelModule i'`. Its forward map composed with
   `kernelModuleι i'` is `b^*(ι) ≫ (pullbackUnitIso b).hom` (`pullbackKernelToKernel_ι`).
3. **Monomorphisms on affine schemes** (`mono_of_injective_top`). On an affine scheme, a
   morphism of invertible modules that is injective on global sections is a monomorphism. Its
   sections over a basic open `D(r)` are the localization at `r` of the global map (FLT
   `isLocalization_basicOpen_of_locallyTrivial`). Basic opens form a basis, so all stalk maps are
   injective (`TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis`), and the Library's
   `mono_of_stalk_injective` applies.
4. **The affine algebra** (`mono_pullback_of_affine_square`, `mono_pullback_of_affine_square_ring`).
   Let `U ⟶ Spec R` be affine and `ι : M ⟶ N` a morphism of invertible modules on `U`. Suppose
   the `R`-linear map on sections is injective with a flat cokernel `C`. Then the pullback of `ι`
   along any cartesian square over `Spec R' ⟶ Spec R` with affine corner is a monomorphism.
   Indeed `R' ⊗_R Γ(M) → R' ⊗_R Γ(N)` is injective (`LinearMap.lTensor_injective_of_exact_of_flat`).
   The Library's `isIso_scalarSectionsBaseChangeMap_of_isPullback_affine` and
   `scalarSectionsBaseChangeMap_naturality` identify it with the global-sections map of the
   pulled-back morphism. Step 3 then concludes.
5. **The concrete chart** (`chartMap`, `mono_chart`). Take an affine open `V ⊆ S` and an affine
   open `U₀ ⊆ f⁻¹ V`, with chart `chartMap f U₀ e = U₀.toSpecΓ ≫ Spec.map (f.appLE V U₀ e)`.
   Its structure ring map is `f.appLE V U₀ e` followed by `U₀.topIso.inv`
   (`structureRingHom_chartMap`), and it lies over `V` (`chartMap_fromSpec`). On `U₀`, the
   restricted ideal inclusion has the following sections:
   - The sections map is the subtype inclusion of the kernel of `i.app` (injective).
   - Its image is exactly the kernel of `i.app (U₀.ι ''ᵁ ⊤)`.
   - That map is surjective (step 1, since `U₀` is affine).
   - Its target `Γ(E, i⁻¹ U₀)` is a `Γ(S, V)`-algebra through `(i ≫ f).appLE`
     (`chart_ringHom_eq`). This algebra is flat because `i ≫ f` is flat
     (`HasRingHomProperty.appLE` for `Flat`).

   Step 4 then gives the monomorphism after any affine base change of the chart.
6. **Globalization** (`mono_pullback_snd_kernelModuleι`). Fix a point `x` of `X_T = T ×_S X`.
   Choose affine opens `V ∋ f(p x)` of `S`, `U₀ ∋ p x` inside `f⁻¹ V`, and `V_T ∋ q x` inside
   `g⁻¹ V`, and let `ψ = g.appLE V V_T`. The chosen pullback `W = Spec Γ(T, V_T) ×_{Spec Γ(S,V)} U₀`
   is affine. The map `j = pullback.map … : W ⟶ X_T` is an open immersion
   (`Scheme.pullback_map_isOpenImmersion`) whose image contains `x` (`Scheme.Pullback.range_map`),
   and `j ≫ p = pullback.snd ≫ U₀.ι`. Along the isomorphisms `pullbackComp`, `pullbackCongr` and
   `restrictFunctorIsoPullback`, step 5 shows that `j^*(p^*(ι))` is a monomorphism. Hence
   `p^*(ι)` is injective on the stalk at `x = j w` (`stalk_injective_of_mono_pullback`, via
   `restrictStalkNatIso`). By `mono_of_stalk_injective`, `p^*(ι)` is a monomorphism.
7. **Conclusion** (`relativeEffectiveDivisorBaseChange`). The square with top map
   `(I.comapIso p).hom ≫ pullback.snd`, sides `(I.comap p).subschemeι` and `i`, and bottom `p` is
   cartesian (`IsPullback.of_iso_pullback` with `pullbackSymmetry`). Step 2, with the
   monomorphism of step 6, gives the required isomorphism and its compatibility with the
   inclusions. The statement's first clause follows from the published
   `RelativeEffectiveDivisorBaseChange.isRelativeEffectiveCartierIdeal_of_kernelIso`.

The rank-one hypothesis enters only through the published
`Picard.isInvertible_of_isLocallyFreeRankOne`, reused from
[NoetherianLineBundleSeesawProof](NoetherianLineBundleSeesawProof.md). It is used for the monomorphism criterion of step 3 on the
charts.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
