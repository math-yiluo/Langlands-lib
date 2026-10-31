# Sheaves of sections over an open, and their restriction maps

Author: Worker 958.

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.Basic`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution`. It supplies the building blocks of the
sheafified Čech complex of `Langlands.AlgebraicGeometry.Modules.CechResolution.Complex`:
for an open `W` of a scheme `X` and an `𝒪_X`-module `M`, the `𝒪_X`-module
`(j_W)_* (M|_W)` whose sections over `V` are the sections of `M` over `W ∩ V`, the unit
`M ⟶ (j_W)_* (M|_W)`, the restriction maps between these modules for `W' ⊆ W`, elementwise
facts about finite biproducts of `𝒪_X`-modules, and a local criterion for exactness.
In the Stacks Project these are the factors `(j_{i_0 … i_p})_* 𝓕_{i_0 … i_p}` of the
complex `𝔆^•(𝒰, 𝓕)` of Cohomology of Sheaves, Lemma `lemma-covering-resolution` (tag 02FU).

All declarations are at an arbitrary universe `u`, with `X : Scheme.{u}`.

## Instance

- `instance : HasFiniteBiproducts X.Modules`, from `Abelian.hasFiniteBiproducts`. Mathlib makes
  that declaration a local instance only, so it is registered here globally for `X.Modules`.

## The sheaf `sheafOn M W`

- `image_preimage_eq W V : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = W ⊓ V` for opens `W V : X.Opens`.
- `sheafOn M W : X.Modules` is
  `(Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.restrictFunctor W.ι).obj M)`, the
  pushforward along the open immersion `W.ι : W ⟶ X` of the restriction of `M` to `W`.
- `sheafOn_obj W V : Γ(sheafOn M W, V) = Γ(M, W.ι ''ᵁ (W.ι ⁻¹ᵁ V))` holds by `rfl`; by
  `image_preimage_eq` the open on the right is `W ⊓ V`. `sheafOn_map` records (by `rfl`) that
  the restriction maps of `sheafOn M W` are restriction maps of `M`.
- `smul_eq W V r m` (by `rfl`): a section `r : Γ(X, V)` acts on `m : Γ(sheafOn M W, V)` as its
  image under `W.ι.app V ≫ (W.ι.appIso (W.ι ⁻¹ᵁ V)).inv`, i.e. as the restriction of `r` to
  `W.ι ''ᵁ (W.ι ⁻¹ᵁ V)`, acting on `M`.
- `unit M W : M ⟶ sheafOn M W` is the unit at `M` of Mathlib's adjunction
  `Scheme.Modules.restrictAdjunction W.ι` (restriction to `W` is left adjoint to pushforward
  along `W.ι`); `unit_app` states (by `rfl`) that its component over `V` is the restriction
  `M(V) ⟶ M(W.ι ''ᵁ W.ι ⁻¹ᵁ V)`.

## Restriction maps `sheafOn M W ⟶ sheafOn M W'` for `W' ≤ W`

- `image_preimage_mono h V` and `image_preimage_mono_right W h` are the monotonicity of
  `W.ι ''ᵁ (W.ι ⁻¹ᵁ V)` in `W` and in `V`.
- `app_appIso_inv_comp_map`, `map_smul_appIso` and `map_comp_map` are the compatibilities of
  these restrictions with the ring maps and with each other that the construction uses.
- `resApp h V` is the restriction `Γ(M, W.ι ''ᵁ W.ι ⁻¹ᵁ V) ⟶ Γ(M, W'.ι ''ᵁ W'.ι ⁻¹ᵁ V)`, and
  `resApp_smul` says it is `Γ(X, V)`-linear.
- `interFunctor X W : X.Opens ⥤ X.Opens` is `V ↦ W.ι ''ᵁ (W.ι ⁻¹ᵁ V)`, and
  `interFunctorMap h : interFunctor X W' ⟶ interFunctor X W` is the inclusion for `W' ≤ W`.
- `resPresheaf M h` is the whiskering of `NatTrans.op (interFunctorMap h)` with `M.presheaf`,
  a morphism of abelian presheaves `(sheafOn M W).presheaf ⟶ (sheafOn M W').presheaf`.
- `res M h : sheafOn M W ⟶ sheafOn M W'` is the morphism of `𝒪_X`-modules built from
  `resPresheaf M h` and `resApp_smul` with `PresheafOfModules.homMk`. The lemmas
  - `res_app h V : (res M h).app V = M.presheaf.map (homOfLE (image_preimage_mono h V)).op`
    (by `rfl`),
  - `res_refl W : res M (le_refl W) = 𝟙 _`,
  - `res_comp h h' : res M h ≫ res M h' = res M (h'.trans h)`,
  - `unit_res h : unit M W ≫ res M h = unit M W'`

  say that these maps are the restrictions of sections, form a functor in `W`, and are
  compatible with the units.

## Elementwise facts

For `M N : X.Modules`:

- `evalApp V x : (M ⟶ N) →+ Γ(N, V)` evaluates morphisms at a section `x` over `V`; hence
  `sum_app_apply` (finite sums of morphisms are evaluated termwise), `zsmul_app_apply`
  (integer multiples), and `comp_app_apply` (composition, by `rfl`).
- `app_injective_of_mono f V`: a monomorphism `f` of `𝒪_X`-modules is injective on sections
  over every open `V` (via the forgetful functor to abelian presheaves).
- `mono_of_app_injective f h`: conversely, `f` is a monomorphism if it is injective on
  sections over every open.
- For a finite family `G : ι → X.Modules` (`[Fintype ι]`):
  - `biproduct_eq_sum_app G V x : x = ∑ i, (biproduct.ι G i).app V ((biproduct.π G i).app V x)`
    for every section `x` of `⨁ G` over `V` (from `IsBilimit.total`, since Mathlib's
    `biproduct.total` needs the index type in `Type`);
  - `biproduct_ext_app G`: sections of `⨁ G` over `V` with equal components are equal;
  - `biproduct_π_app_sum_ι_app G V y j` and `biproduct_exists_app G V y`: every family
    `y : ∀ i, Γ(G i, V)` is the family of components of a section of `⨁ G` over `V`.

  So `Γ(⨁ G, V)` is identified with `∀ i, Γ(G i, V)` through the projections.

## Local exactness criterion

`exact_of_locally S h`: a short complex `S : ShortComplex X.Modules` is exact if, for every
open `V`, every `c : Γ(S.X₂, V)` with `S.g.app V c = 0` and every point `x ∈ V`, there are an
open `W ≤ V` containing `x` and `b : Γ(S.X₁, W)` with `S.f.app W b` equal to the restriction of
`c` to `W`.

Proof: by `ShortComplex.exact_iff_epi_kernel_lift` it suffices that
`kernel.lift S.g S.f S.zero : S.X₁ ⟶ kernel S.g` is an epimorphism. The Library lemma
`ClosedImmersionHigherDirectImageVanishing.epi_of_isLocallySurjective` reduces this to local
surjectivity of the underlying map of abelian presheaves
(`TopCat.Presheaf.isLocallySurjective_iff`). A section `z` of `kernel S.g` over `V` maps to a
section `c` of `S.X₂` with `S.g.app V c = 0`; the hypothesis gives `W`, `b`, and the required
equality in `kernel S.g` is checked after the injective map `(kernel.ι S.g).app W`
(`app_injective_of_mono`), using `kernel.lift_ι` and the naturality of `kernel.ι S.g`.

## Provenance

The construction is the factor `(j_{i_0 … i_p})_* 𝓕_{i_0 … i_p}` of the complex
`𝔆^•(𝒰, 𝓕)` of Stacks Project, Cohomology of Sheaves, Lemma
`lemma-covering-resolution` (tag 02FU), in `cohomology.tex` (statement from line 4571) of the
registered folder `stacks-flasque-affine-vanishing-kunneth-a04446e5` (Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). The local exactness criterion is the stalkwise
exactness check of that proof, phrased with sections instead of stalks. The Lean
formulations, the auxiliary lemmas and their proofs are this module's own.
