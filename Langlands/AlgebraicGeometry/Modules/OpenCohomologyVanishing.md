# Vanishing of higher direct images from cohomology over preimages of basic opens

Module `Langlands.AlgebraicGeometry.Modules.OpenCohomologyVanishing`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. Technical lemmas are in the
sub-namespace `OpenCohomologyVanishing`.

## Definition

```lean
noncomputable def openCohomology (U : X.Opens) (n : ℕ) : X.Modules ⥤ ModuleCat.{u} Γ(U, ⊤) :=
  Scheme.Modules.restrictFunctor U.ι ⋙ cohomology U n
```

For a scheme `X : Scheme.{u}`, an open `U` of `X` and `n : ℕ`, this functor sends an
`𝒪_X`-module `M` to `Hⁿ(U, M|_U)`. Here `M|_U` is Mathlib's restriction
`(Scheme.Modules.restrictFunctor U.ι).obj M` along the open immersion `U.ι : U ⟶ X`, and
`cohomology U n` is the published sheaf cohomology functor
`Langlands.AlgebraicGeometry.Modules.DerivedSections.cohomology` of the scheme `U`. Its values
are modules over `Γ(U, ⊤)`, the ring of global functions of the scheme `U`. This is the usual
cohomology `Hⁿ(U, M)` of `M` over the open `U`, and the definition just gives it a name. In
the results below, `U` is the preimage `f ⁻¹ᵁ W` of an open `W` of the target.

## Main results

All results take `f : X ⟶ Y` a morphism of schemes in `Scheme.{u}`, `n : ℕ` and
`M : X.Modules`. `higherDirectImage f n` is the published `Rⁿ f_*` from `DerivedSections`.
`Opens.IsBasis B` is Mathlib's notion that `B` is a basis of the topology of `Y`.

```lean
theorem isZero_restrict_higherDirectImage_of_isBasis (f : X ⟶ Y) (V : Y.Opens)
    {B : Set Y.Opens} (hB : Opens.IsBasis B) (n : ℕ) (M : X.Modules)
    (h : ∀ U ∈ B, U ≤ V → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj ((higherDirectImage f n).obj M))
```

If `Hⁿ(f⁻¹ U, M) = 0` for every member `U` of a basis `B` with `U ⊆ V`, then the restriction
of `Rⁿ f_* M` to the open `V` is zero.

- `isZero_pullback_higherDirectImage_of_isBasis`: the same hypotheses give
  `IsZero ((Scheme.Modules.pullback V.ι).obj ((higherDirectImage f n).obj M))`. The proof
  transports the previous result along Mathlib's `Scheme.Modules.restrictFunctorIsoPullback`.
- `isZero_pullback_higherDirectImage_of_affineOpens`: the same conclusion, with the hypothesis
  `∀ U : Y.Opens, IsAffineOpen U → U ≤ V → IsZero ((openCohomology (f ⁻¹ᵁ U) n).obj M)`. It
  applies the previous result to the basis of affine opens, `Y.isBasis_affineOpens`.
- `isZero_higherDirectImage_of_isBasis`: if `Hⁿ(f⁻¹ U, M) = 0` for every `U ∈ B`, then
  `IsZero ((higherDirectImage f n).obj M)`.
- `isZero_higherDirectImage_of_affineOpens`: if `Hⁿ(f⁻¹ U, M) = 0` for every affine open `U`
  of `Y`, then `IsZero ((higherDirectImage f n).obj M)`.

Each statement is about one degree `n` and has no hypothesis on `f` or on `M`.

## Provenance

The definition `openCohomology` is an internal convenience name for the composite of two
existing functors. It is the cohomology `Hⁿ(U, -)` of an open, which the source writes as
`Hⁱ(f⁻¹(V), F)`.

The theorems are derived consequences of Stacks, Cohomology of Sheaves, Lemma
`lemma-describe-higher-direct-images` (tag 01E4), together with Lemma
`lemma-localize-higher-direct-images` (tag 01E5). See `cohomology.tex` at git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, lines 591–651, in the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`. Lemma 01E4 says that `Rⁱ f_* F` is the
sheaf associated to the presheaf `V ↦ Hⁱ(f⁻¹(V), F)`. When this presheaf vanishes on a basis
of the opens contained in `V`, every germ at a point of `V` is zero, so the restriction of the
associated sheaf to `V` is zero. The four comments on the tag 01E4 web page (retained in the
registered source `stacks-affine-morphisms-relative-vanishing-a04446e5`) concern the proof and
do not change the statement.

The Library does not have the presheaf description of tag 01E4. So the Lean proof does not use
it and does a dimension shift instead. That argument uses Stacks Lemmas
`lemma-injective-flasque` (tag 09SX: injective modules are flasque) and `lemma-flasque-acyclic`
(tag 09SY: flasque modules have vanishing higher cohomology on every open). See
`cohomology.tex` lines 1902–1916 of the same source. Both are already in the Library as
`PushforwardInjectiveAcyclic.isFlasque_of_injective` and
`PushforwardInjectiveAcyclic.isZero_cohomology_succ_of_isFlasque`. The formal statements and
the proof route are internal.

## Proof

Supporting lemmas, in the sub-namespace `OpenCohomologyVanishing`:

- `preservesFiniteLimits_pushforward`: pushforward of sheaves of modules along a continuous
  functor between small sites preserves finite limits. Composed with the forgetful functor to
  presheaves of modules, it equals presheaf pushforward followed by forgetting. Presheaf
  pushforward is a right adjoint (Mathlib's `PresheafOfModules.pullbackObjIsDefined_eq_top`),
  and forgetting reflects finite limits. The resulting instance says that
  `Scheme.Modules.restrictFunctor U.ι` is left exact, so restriction to `U` preserves short
  exact sequences.
- `isFlasque_restrict`: the restriction of a flasque module to an open is flasque, because
  `Scheme.Modules.restrict_map` identifies the restriction maps of `M|_U` with those of `M`.
- `isZero_of_subsingleton`: a module all of whose groups of sections are trivial is zero.
- `eq_zero_of_locally_eq_zero`: a section that vanishes locally is zero (the sheaf property,
  through `TopCat.Sheaf.eq_of_locally_eq'`).
- `eq_zero_of_epi`: if `N₁ ⟶ N₂` is an epimorphism and `N₁` has no nonzero sections over the
  opens contained in `V`, then neither has `N₂`. Epimorphisms are locally surjective
  (`ClosedImmersionHigherDirectImageVanishing.isLocallySurjective_of_epi`).
- `eq_zero_of_comp_eq_zero`: let `φ ≫ ψ = 0` with `ψ : N₂ ⟶ N₃` an epimorphism, and suppose
  that over the opens contained in `V`, sections of `N₂` lie locally in the image of `φ`. Then
  `N₃` has no nonzero sections over opens contained in `V`.
- `surjective_app_of_isZero`: for a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of
  `𝒪_X`-modules and an open `W` with `H¹(W, M₁) = 0`, the map `M₂(W) → M₃(W)` is surjective. It
  restricts the sequence to `W` and applies the published
  `DerivedPlus.epi_rightDerived_zero_map_of_isZero` to the global sections functor of `W`.
- `subsingleton_of_isZero`: `H⁰(W, M) = 0` implies that `M(W)` is trivial, through the
  published `cohomologyZeroIso`.
- `isZero_openCohomology_X₃`: for a short exact sequence with flasque middle term,
  `Hⁿ⁺²(W, M₁) = 0` implies `Hⁿ⁺¹(W, M₃) = 0`. The restricted middle term is flasque, so its
  `Hⁿ⁺¹` vanishes. Hence the connecting map `Hⁿ⁺¹(W, M₃) → Hⁿ⁺²(W, M₁)` is a monomorphism
  (`DerivedPlus.mono_rightDerivedδ_of_isZero`), and its target is zero.

Core lemma `eq_zero_of_isBasis`: under the hypotheses of the main theorem, every section of
`Rⁿ f_* M` over an open `O ⊆ V` is zero. The proof is by induction on `n`, for all `M` at once.

- `n = 0`: `R⁰ f_* M ≅ f_* M`, and a section of `f_* M` over `O` is a section of `M` over
  `f⁻¹ O`. Every point of `O` has a basic neighbourhood `U ⊆ O`. The restriction of the section
  to `f⁻¹ U` vanishes because `H⁰(f⁻¹ U, M) = 0`. Hence the section vanishes by the sheaf
  property, and so does its image under the epimorphism `f_* M ⟶ R⁰ f_* M`.
- `n = 1`: embed `M` in an injective `I` with cokernel `C`
  (`PushforwardInjectiveAcyclic.injectiveSc`). Since `R¹ f_* I = 0`, the connecting map
  `δ : R⁰ f_* C ⟶ R¹ f_* M` is an epimorphism. Precomposed with `f_* C ≅ R⁰ f_* C`, it gives
  an epimorphism `ψ : f_* C ⟶ R¹ f_* M` with `f_* I ⟶ f_* C ⟶ R¹ f_* M` zero
  (`DerivedPlus.rightDerived_map_comp_δ`). Over a
  basic `U ⊆ V`, `H¹(f⁻¹ U, M) = 0` makes `I(f⁻¹ U) → C(f⁻¹ U)` surjective. So sections of
  `f_* C` over opens in `V` lie locally in the image of `f_* I`, and `eq_zero_of_comp_eq_zero`
  applies.
- `n = m + 2`: with the same sequence, `Rᵐ⁺² f_* I = 0`, so `δ : Rᵐ⁺¹ f_* C ⟶ Rᵐ⁺² f_* M`
  is an epimorphism. `I` is flasque, so `isZero_openCohomology_X₃` turns the hypothesis
  `Hᵐ⁺²(f⁻¹ U, M) = 0` into `Hᵐ⁺¹(f⁻¹ U, C) = 0`. The induction hypothesis applied to `C`
  kills the sections of `Rᵐ⁺¹ f_* C` over opens in `V`, and `eq_zero_of_epi` transfers this to
  `Rᵐ⁺² f_* M`.

Main theorems. Sections of `(Rⁿ f_* M)|_V` over an open `W` of `V` are sections of `Rⁿ f_* M`
over the image `V.ι ''ᵁ W ⊆ V`, so they vanish by the core lemma, and the restriction is zero.
For the global versions take `V = ⊤`.

The proof uses no `sorry` and no axioms beyond Lean's standard `propext`, `Classical.choice`
and `Quot.sound`.

## Intended use

This is the local-to-global zero detection step for the proof of
`Langlands.AbelianScheme.AlgClosedFieldSquareFirstProjectionAcyclicityStatement` (task
`651d1a6b-549e-4d79-ae47-19627b02f30d`). It reduces vanishing of `Rⁿ f_*` (or of its pullback
to an open `V`) to vanishing of the cohomology of preimages of affine opens. The module proves
nothing about base change, perfect complexes or fibres.
