# Extension of scalars of isotypic parts

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextScalarExtension` (`baseChangeLift`,
`IsSemilinear`, `abutmentMap`, `cohomologyHomMap`, the base-change maps
`abutmentBaseChangeMap`, `cohomologyHomBaseChangeMap`,
`smoothRepExtendScalars_isSemilinear`; Worker 61) and
`Langlands.Cohomology.HyperextDegenerationIsotypic` (`isotypicPart`,
`isotypicRepresentation`, `isotypicIntertwiningMap`, `abutmentRepresentation`,
`cohomologyHomRepresentation`; Worker 61). Through these imports it also uses
`baseChangeRepresentation` of `Langlands.Cohomology.DivisibleSystem.ScalarExtension`
(Worker 61), the actions `abutmentAction`, `cohomologyHomAction` of
`Langlands.Cohomology.HyperextDegenerationEquivariance` (Worker 61) and
`exactDerivedHomologyIso` of `Langlands.Cohomology.ExactDerivedHomology`
(Worker 13).

Let `R → S` be an algebra of commutative rings (`[Algebra R S]`) and `Γ` a
group. The module `HyperextDegenerationIsotypic` attaches to representations
`τ` and `ρ` of `Γ` over `R` the `τ`-isotypic part of `ρ`, the sum of the images
of all intertwining maps `τ → ρ`, and makes the actions of `Γ` on the abutment
`Hom(K, W₀⟦n⟧)` and on `Hom(H^{-n} K, W)` into representations; here `K` is an
object of the derived category of an `R`-linear abelian category `C`, `W` an
object of `C`, `W₀` the complex `W` placed in degree `0`, and `Γ` acts on `K`
and `W` by automorphisms. The module `HyperextScalarExtension` defines, for an
exact functor `F` that is semilinear along `R → S`, `S`-linear base-change maps
`S ⊗[R] Hom(K, W₀⟦n⟧) → Hom(F K, (F W)₀⟦n⟧)` and
`S ⊗[R] Hom(H^q K, W) → Hom(H^q (F K), F W)`, where `F K` is
`F.mapDerivedCategory.obj K`.

This module

- defines, for representations over `R`, `S`-linear maps from the extension of
  scalars of a `τ`-isotypic part, of the invariants and of the multiplicity
  space `Hom_Γ(τ, ρ)` to the corresponding objects for the extensions of
  scalars `S ⊗[R] τ` and `S ⊗[R] ρ`, and proves the first two injective when
  `S` is flat over `R`;
- proves that the base-change maps of `HyperextScalarExtension` intertwine the
  representations of `Γ` over `R` with the representations over `S` induced by
  `F`, and restricts them to `τ`-isotypic parts.

None of these maps is proved to be surjective or bijective, and the module
makes no claim that extension of scalars commutes with isotypic parts or with
invariants (see Scope for an example where it does not).

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`
and use the Library's `HyperextAbutment` namespace (`open HyperextAbutment`).
For a representation `ρ` of `Γ` over `R` on `V`, `S ⊗[R] ρ` below denotes the
Library's `baseChangeRepresentation S ρ`, the representation on `S ⊗[R] V` in
which `γ` acts by `(ρ γ).baseChange S`; `Hom_Γ(τ, ρ)` denotes Mathlib's
`τ.IntertwiningMap ρ`, and `ρ^Γ` Mathlib's `ρ.invariants`.

## Isotypic parts, invariants and multiplicity spaces

Section `Algebra` takes `R : Type uR` and `S : Type uS` commutative rings with
`[Algebra R S]` (`S` explicit), a group `Γ : Type uΓ`, `R`-modules `U`, `V`,
`W`, and representations `τ : Representation R Γ U`,
`ρ : Representation R Γ V`, `σ : Representation R Γ W`.

| Declaration | Statement |
| --- | --- |
| `baseChangeIntertwiningMap S f` | For `f : Hom_Γ(τ, ρ)`, the intertwining map `S ⊗[R] τ → S ⊗[R] ρ` whose underlying linear map is `f.toLinearMap.baseChange S`. A `def`. |
| `baseChangeIntertwiningMap_tmul S f s u` | `baseChangeIntertwiningMap S f (s ⊗ₜ u) = s ⊗ₜ f u` (a `simp` lemma, by definition). |
| `multiplicityBaseChangeMap S τ ρ` | The `S`-linear map `S ⊗[R] Hom_Γ(τ, ρ) →ₗ[S] Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)`. A `def`. |
| `multiplicityBaseChangeMap_tmul S τ ρ s f` | `multiplicityBaseChangeMap S τ ρ (s ⊗ₜ f) = s • baseChangeIntertwiningMap S f` (a `simp` lemma, by definition). |
| `tmul_mem_isotypicPart S τ s hv` | If `v` lies in `isotypicPart τ ρ`, then `s ⊗ₜ v` lies in `isotypicPart (S ⊗[R] τ) (S ⊗[R] ρ)`. |
| `isotypicBaseChangeMap S τ ρ` | The `S`-linear map `S ⊗[R] isotypicPart τ ρ →ₗ[S] isotypicPart (S ⊗[R] τ) (S ⊗[R] ρ)`, `s ⊗ v ↦ s ⊗ v`. A `def`. |
| `coe_isotypicBaseChangeMap_tmul S τ ρ s v` | The image of `s ⊗ₜ v`, as an element of `S ⊗[R] V`, is `s ⊗ₜ (v : V)` (a `simp` lemma, by definition). |
| `coe_isotypicBaseChangeMap S τ ρ x` | The image of `x`, as an element of `S ⊗[R] V`, is `(isotypicPart τ ρ).subtype.baseChange S x`. |
| `isotypicBaseChangeMap_injective S τ ρ` | If `[Module.Flat R S]`, then `isotypicBaseChangeMap S τ ρ` is injective. |
| `isotypicBaseChangeIntertwiningMap S τ ρ` | The intertwining map from `baseChangeRepresentation S (isotypicRepresentation τ ρ)` to `isotypicRepresentation (S ⊗[R] τ) (S ⊗[R] ρ)` with underlying linear map `isotypicBaseChangeMap S τ ρ`. A `def`. |
| `isotypicBaseChangeMap_naturality S τ φ x` | For `φ : Hom_Γ(ρ, σ)` and `x : S ⊗[R] isotypicPart τ ρ`: `isotypicIntertwiningMap (S ⊗[R] τ) (baseChangeIntertwiningMap S φ) (isotypicBaseChangeMap S τ ρ x) = isotypicBaseChangeMap S τ σ ((isotypicIntertwiningMap τ φ).toLinearMap.baseChange S x)`. |
| `tmul_mem_invariants S s hv` | If `v ∈ ρ^Γ`, then `s ⊗ₜ v ∈ (S ⊗[R] ρ)^Γ`. |
| `invariantsBaseChangeMap S ρ` | The `S`-linear map `S ⊗[R] ρ^Γ →ₗ[S] (S ⊗[R] ρ)^Γ`, `s ⊗ v ↦ s ⊗ v`. A `def`. |
| `coe_invariantsBaseChangeMap_tmul S ρ s v` | The image of `s ⊗ₜ v`, as an element of `S ⊗[R] V`, is `s ⊗ₜ (v : V)` (a `simp` lemma, by definition). |
| `invariantsBaseChangeMap_injective S ρ` | If `[Module.Flat R S]`, then `invariantsBaseChangeMap S ρ` is injective. |

Proofs.

- `baseChangeIntertwiningMap`: the identity `f ∘ τ γ = ρ γ ∘ f` is base-changed
  with Mathlib's `LinearMap.baseChange_comp`.
- `multiplicityBaseChangeMap` is the Library's `baseChangeLift` of the additive
  map `f ↦ baseChangeIntertwiningMap S f` (additive by
  `LinearMap.baseChange_zero` and `LinearMap.baseChange_add`). Its
  semilinearity, `baseChangeIntertwiningMap S (r • f) = algebraMap R S r • baseChangeIntertwiningMap S f`,
  is checked on pure tensors (`TensorProduct.inductionOn`), where it is
  `s ⊗ (r • f u) = algebraMap R S r • (s ⊗ f u)`.
- `tmul_mem_isotypicPart`: by the Library's `isotypicPart_le_iff`, it suffices
  that `s ⊗ₜ f u` lies in the target for every `f : Hom_Γ(τ, ρ)` and `u : U`;
  this element is `baseChangeIntertwiningMap S f (s ⊗ₜ u)`, which lies there by
  `apply_mem_isotypicPart`.
- `isotypicBaseChangeMap` and `invariantsBaseChangeMap` are Mathlib's
  `LinearMap.codRestrict` of the base change of the inclusion of the
  submodule; that the image lies in the target submodule is checked on pure
  tensors (`tmul_mem_isotypicPart`, `tmul_mem_invariants`) and is preserved by
  sums.
- The injectivity statements: by `LinearMap.baseChange_eq_ltensor` the base
  change of the injective inclusion is `lTensor S` of it, which is injective for
  flat `S` (`Module.Flat.lTensor_preserves_injective_linearMap`); the
  restriction of the codomain does not change the underlying map.
- `isotypicBaseChangeIntertwiningMap` and
  `isotypicBaseChangeMap_naturality`: both sides agree on pure tensors by
  definition, and both sides are additive.
- `tmul_mem_invariants`: `γ` sends `s ⊗ₜ v` to `s ⊗ₜ ρ γ v = s ⊗ₜ v`
  (`baseChangeRepresentation_apply_tmul`).

## Base-change maps and the actions of Γ

Section `Derived` takes `R : Type uR`, `S : Type uS` with `[Algebra R S]`, an
`R`-linear abelian category `C : Type uC` (`[Category.{vC} C] [Abelian C] [Linear R C]`,
`[HasDerivedCategory.{s} C]`), an `S`-linear abelian category `D : Type uD`
(`[Category.{vD} D] [Abelian D] [Linear S D]`, `[HasDerivedCategory.{s'} D]`),
a functor `F : C ⥤ D` with `[F.Additive]`, `[PreservesFiniteLimits F]` and
`[PreservesFiniteColimits F]` (so `F` is exact), and a group `Γ : Type uΓ`.
Below `K, K'` are objects of `DerivedCategory C`, `W` an object of `C`,
`n : ℤ`, `ρ : Γ →* Aut K` and `σ : Γ →* Aut W`. The actions induced by `F` are
`ρ_F = (F.mapDerivedCategory.mapAut K).comp ρ : Γ →* Aut (F K)` and
`σ_F = (F.mapAut W).comp σ : Γ →* Aut (F W)`.

| Declaration | Statement |
| --- | --- |
| `abutmentMap_precomp F φ W n f` | For `φ : K' ⟶ K` and `f : ShiftedHom K W₀ n`: `abutmentMap F K' W n (φ ≫ f) = F.mapDerivedCategory.map φ ≫ abutmentMap F K W n f`. |
| `abutmentMap_abutmentAction F ρ σ n γ f` | `abutmentMap F K W n (abutmentAction ρ σ n γ f) = abutmentAction ρ_F σ_F n γ (abutmentMap F K W n f)`. |
| `cohomologyHomMap_cohomologyHomAction F ρ σ n γ g` | For `g : H^{-n} K ⟶ W`: `cohomologyHomMap F K W (-n) (cohomologyHomAction ρ σ n γ g) = cohomologyHomAction ρ_F σ_F n γ (cohomologyHomMap F K W (-n) g)`. |

Now also `hF : IsSemilinear R S F`, and `τ : Representation R Γ U` for an
`R`-module `U`.

| Declaration | Statement |
| --- | --- |
| `abutmentBaseChangeIntertwiningMap F hF ρ σ n` | The intertwining map from `baseChangeRepresentation S (abutmentRepresentation R ρ σ n)` to `abutmentRepresentation S ρ_F σ_F n` with underlying linear map `abutmentBaseChangeMap F hF K W n`. A `def`. |
| `cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n` | The intertwining map from `baseChangeRepresentation S (cohomologyHomRepresentation R ρ σ n)` to `cohomologyHomRepresentation S ρ_F σ_F n` with underlying linear map `cohomologyHomBaseChangeMap F hF K W (-n)`. A `def`. |
| `abutmentIsotypicBaseChangeMap F hF ρ σ n τ` | The `S`-linear map `S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n) →ₗ[S] isotypicPart (S ⊗[R] τ) (abutmentRepresentation S ρ_F σ_F n)`: `isotypicBaseChangeMap` followed by the restriction of `abutmentBaseChangeIntertwiningMap` to isotypic parts (`isotypicIntertwiningMap`). A `def`. |
| `coe_abutmentIsotypicBaseChangeMap_tmul F hF ρ σ n τ s f` | The image of `s ⊗ₜ f`, as an element of `ShiftedHom (F K) (F W)₀ n`, is `s • abutmentMap F K W n f` (a `simp` lemma, by definition). |
| `cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ` | The `S`-linear map `S ⊗[R] isotypicPart τ (cohomologyHomRepresentation R ρ σ n) →ₗ[S] isotypicPart (S ⊗[R] τ) (cohomologyHomRepresentation S ρ_F σ_F n)`, built in the same way from `cohomologyHomBaseChangeIntertwiningMap`. A `def`. |
| `coe_cohomologyHomIsotypicBaseChangeMap_tmul F hF ρ σ n τ s g` | The image of `s ⊗ₜ g`, as a morphism `H^{-n}(F K) ⟶ F W`, is `s • cohomologyHomMap F K W (-n) g` (a `simp` lemma, by definition). |

Proofs.

- `abutmentMap_precomp`: unfold `abutmentMap_apply` and Mathlib's
  `ShiftedHom.map`; then `Functor.map_comp` and associativity.
- `abutmentMap_abutmentAction`: `abutmentAction_apply` writes the action as
  precomposition with `(ρ γ).inv` followed by postcomposition with the image of
  `(σ γ).hom`. The Library's `abutmentMap_comp_single` and `abutmentMap_precomp`
  move both through `abutmentMap`; the remaining equality holds by definition,
  since `(ρ_F γ).inv` is `F.mapDerivedCategory.map (ρ γ).inv` and
  `(σ_F γ).hom` is `F.map (σ γ).hom`.
- `cohomologyHomMap_cohomologyHomAction`: after unfolding
  (`cohomologyHomAction_apply`, `cohomologyHomMap_apply`, `Functor.map_comp`),
  the statement is the naturality of `(exactDerivedHomologyIso F (-n)).hom` at
  `(ρ γ).inv`, up to associativity.
- `abutmentBaseChangeIntertwiningMap`, `cohomologyHomBaseChangeIntertwiningMap`:
  on pure tensors `s ⊗ₜ f`, by `abutmentBaseChangeMap_tmul` (resp.
  `cohomologyHomBaseChangeMap_tmul`), `S`-linearity of the action over `S` and
  the two lemmas above; both sides are additive.
- The isotypic maps are composites, and their `tmul` lemmas hold by
  definition.

## Smooth representations

Section `Smooth` takes `R : Type uR` and `S : Type uS` with `[Algebra R S]` and
`[Module.Flat R S]`, a topological group `G : Type uG`, instances
`HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)` and
`HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)`, a group `Γ`, `K`,
`W`, `ρ`, `σ`, `n` and `τ` as above with `C` the category
`SmoothRep.{uR, uG, w} R G` of smooth representations of `G` over `R`. Write
`E = smoothRepExtendScalars.{w} R S G` for the Library's extension of scalars
of smooth representations, which is exact for flat `S`
(`HyperextScalarExtension`) and semilinear
(`smoothRepExtendScalars_isSemilinear`).

| Declaration | Statement |
| --- | --- |
| `smoothAbutmentIsotypicBaseChangeMap R S G ρ σ n τ` | `abutmentIsotypicBaseChangeMap E (smoothRepExtendScalars_isSemilinear R S G) ρ σ n τ`: the `S`-linear map from `S ⊗[R]` the `τ`-isotypic part of `abutmentRepresentation R ρ σ n` to the `S ⊗[R] τ`-isotypic part of `abutmentRepresentation S ((E.mapDerivedCategory.mapAut K).comp ρ) ((E.mapAut W).comp σ) n`. A `def`. |
| `smoothCohomologyHomIsotypicBaseChangeMap R S G ρ σ n τ` | `cohomologyHomIsotypicBaseChangeMap E (smoothRepExtendScalars_isSemilinear R S G) ρ σ n τ`, with the analogous source and target for `cohomologyHomRepresentation`. A `def`. |

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. Worker 13, the first executor of the task, asked Worker 61 for the
change of coefficients from `𝒪` to `L_ℓ` and for the maps it induces on the
degeneration of Harris's spectral sequence and on its isotypic parts, with any
failure of extension of scalars to commute with isotypic parts kept as an
explicit obligation. The modules `HyperextScalarExtension` and
`HyperextScalarEdgeMap` treat the comparison maps without group actions; this
module adds the actions and the isotypic parts.

For this module Worker 61 read the following passages of Harris 1999, in the
rendered scans (the text layer of this scan is unreliable):

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §5, printed p.312 (one-based PDF page 14): "Using Proposition 4.10, we can
  now apply the arguments of [H1] and [H2, App.] to express the representation
  of the decomposition group `Z_v` on the `JL(π_f)`-isotypic component of
  `H^{n-1}(S̄_{K(N)}, W̃)`, which we denote `H^{n-1}(S̄_{K(N)}, W̃)[π]`." Later on
  the same page: "since `π_v` is supercuspidal, the higher Ext's vanish and the
  spectral sequence (4.10.1) degenerates to an isomorphism (5.2)
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_{K(N)}, W̃)[π]`".
- §3, printed p.307 (one-based PDF page 9), as quoted in the Markdown file of
  `Langlands.Cohomology.HyperextScalarExtension`: "Let `𝒪` denote the ring of
  integers of `L_ℓ` …".

Interpretation (explanation only). Both sides of (5.2) are isotypic parts:
`[π^v]` and `[JL(π_v)]` on the left, `[π]` on the right, while the cohomology
`H_c(M̆_N, 𝒪(n - 1))` is integral and `𝒜_ℓ(GJ, ρ, H)` and `W̃` have
`L_ℓ`-coefficients. With `R = 𝒪`, `S = L_ℓ` and extension of scalars as `F`,
the maps of this module go from `L_ℓ ⊗_𝒪` (an isotypic part over `𝒪`) to the
corresponding isotypic part over `L_ℓ`, compatibly with the actions of the
group `Γ` that acts on `K` and `W`. The group `Γ` and the representation `τ` are
arbitrary; the formalization does not identify them, `K`, `W` or the isotypic
parts with Harris's objects.

## Scope

- No map of this module is proved to be surjective or bijective. Extension of
  scalars need not commute with invariants or isotypic parts, even along a flat
  map. Example (explanation only, not formalized): let `R = ℤ_ℓ`, `S = ℚ_ℓ`,
  `T = ℚ_ℓ/ℤ_ℓ`, and let the group `Γ = T` act on `V = ℤ_ℓ ⊕ T` by
  `γ · (a, t) = (a, t + aγ)`. Since `aT = T ≠ 0` for every nonzero `a ∈ ℤ_ℓ`
  (`T` is divisible), `V^Γ = 0 ⊕ T`, so `ℚ_ℓ ⊗ V^Γ = 0`, while `ℚ_ℓ ⊗ V ≅ ℚ_ℓ`
  with trivial action has invariants `ℚ_ℓ`; so `invariantsBaseChangeMap` is
  `0 → ℚ_ℓ`. The invariants are the isotypic part of the trivial representation
  of `Γ` on `R` (`isotypicPart_trivial`), its extension of scalars is the
  trivial representation on `S ⊗[R] R ≅ S`, and the isotypic part of that
  representation in `S ⊗[R] ρ` is again `(S ⊗[R] ρ)^Γ`; so
  `isotypicBaseChangeMap` for this `τ` is not surjective either. Whether the
  maps are bijective in Harris's situation remains an open obligation.
- The module proves injectivity only for `isotypicBaseChangeMap` and
  `invariantsBaseChangeMap`, under `[Module.Flat R S]`; the maps on abutments
  and on `Hom(H^{-n} K, W)` are composites with base-change maps whose
  injectivity is not established.
- The compatibility of these maps with the degeneration isomorphisms on
  isotypic parts (`degenerationIsotypicEquiv`) is not proved here.
- The geometric inputs of Harris's Proposition 4.10 and (5.2), the groups and
  representations that cut out the isotypic parts, and their identification
  with `Γ`, `τ`, `K` and `W` are not formalized.
- `HasDerivedCategory` is a hypothesis; the results hold for each such
  instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.312 (rendered scan) read for this module; printed p.307 as quoted in
`Langlands.Cohomology.HyperextScalarExtension`.

Dependencies: `Langlands.Cohomology.HyperextScalarExtension` and
`Langlands.Cohomology.HyperextDegenerationIsotypic`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
