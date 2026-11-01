# Extension of scalars and comparison maps on hyperext groups

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension`
(`smoothRepExtendScalars`; Worker 61), through it
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (`repExtendScalars`;
Worker 61), `Langlands.Cohomology.ExactDerivedHomology`
(`exactDerivedHomologyIso`; Worker 13) and
`Langlands.Representation.Category.Abelian` (the abelian structure of smooth
representations and the closure of `smoothRepProperty` under kernels and
cokernels; Worker 13).

Let `R → S` be an algebra of commutative rings (`[Algebra R S]`). The Library's
degeneration of the hyperext spectral sequence compares, for an object `K` of
the derived category of an abelian category `C` and an object `W` of `C`, the
group `Hom(K, W₀⟦n⟧)` with `Hom(H^{-n} K, W)`, where `W₀` is `W` placed in
degree `0` and `H^q` is the cohomology functor in degree `q` (the edge map
`HyperextDegeneration.edgeMap`). This module compares these groups, and the
groups `Ext^n(X, Y)`, over `R` with the corresponding groups over `S`.

For an exact functor `F` from an `R`-linear abelian category to an `S`-linear
abelian category with `F.map (r • f) = algebraMap R S r • F.map f`, it defines
`S`-linear comparison maps

- `S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)`,
- `S ⊗[R] Hom(K, W₀⟦n⟧) → Hom(F K, (F W)₀⟦n⟧)`,
- `S ⊗[R] Hom(H^q K, W) → Hom(H^q (F K), F W)`,

where on derived categories `F K` means `F.mapDerivedCategory.obj K`, Mathlib's
derived functor of the exact functor `F`. Extension of scalars `V ↦ S ⊗[R] V`
of representations and of smooth representations is such a functor when `S` is
flat over `R`. The comparison maps are not claimed to be isomorphisms, and the
module proves no isomorphism, injectivity or surjectivity statement about them.

## Exactness of extension of scalars

Section `Exact` takes commutative rings `R : Type uR`, `S : Type uS` with
`[Algebra R S]` and a monoid `G : Type uG`. The functor
`repExtendScalars.{w} R S G : Rep.{w} R G ⥤ Rep.{max uS w} S G` of the Library
sends a representation `V` to `S ⊗[R] V`. Section `SmoothExact` takes a
topological group `G` instead, and the functor
`smoothRepExtendScalars.{w} R S G : SmoothRep.{uR, uG, w} R G ⥤ SmoothRep.{uS, uG, max uS w} S G`.

| Declaration | Statement |
| --- | --- |
| `repExtendScalars_map_exact R S G T hT` | If `[Module.Flat R S]` and `T` is an exact short complex in `Rep.{w} R G`, then its image under `repExtendScalars R S G` is exact. |
| `repExtendScalars_preservesHomology`, `repExtendScalars_preservesFiniteLimits`, `repExtendScalars_preservesFiniteColimits` | Instances, for `[Module.Flat R S]`: `repExtendScalars R S G` preserves homology, finite limits and finite colimits. |
| `smoothRepToRep_preservesHomology` | Instance: the inclusion `SmoothRep.toRep : SmoothRep.{uR, uG, w} R G ⥤ Rep.{w} R G` preserves homology. |
| `smoothRepExtendScalars_map_exact R S G T hT` | If `[Module.Flat R S]` and `T` is an exact short complex of smooth representations, then its image under `smoothRepExtendScalars R S G` is exact. |
| `smoothRepExtendScalars_preservesHomology`, `smoothRepExtendScalars_preservesFiniteLimits`, `smoothRepExtendScalars_preservesFiniteColimits` | Instances, for `[Module.Flat R S]`: `smoothRepExtendScalars R S G` preserves homology, finite limits and finite colimits. |

With these instances the functors are exact, so Mathlib's
`Functor.mapDerivedCategory`, `Abelian.Ext.mapExactFunctor` and
`Functor.mapDerivedCategorySingleFunctor` apply to them.

Proofs.

- `repExtendScalars_map_exact`: the forgetful functors `Rep R G ⥤ ModuleCat R`
  and `Rep S G ⥤ ModuleCat S` are faithful and preserve homology, so
  exactness of both short complexes can be tested on underlying modules
  (`ShortComplex.exact_map_iff_of_faithful`) and rewritten as Mathlib's
  `LinearMap.Exact` (`ShortComplex.moduleCat_exact_iff_range_eq_ker`,
  `LinearMap.exact_iff`). Flatness gives exactness of `S ⊗[R] -`
  (`Module.Flat.lTensor_exact`), and `LinearMap.baseChange_eq_ltensor` identifies
  `lTensor S` with the base change computed by `repExtendScalars`.
- The `repExtendScalars` instances are Mathlib's
  `Functor.preservesHomology_of_map_exact`,
  `Functor.preservesFiniteLimits_of_preservesHomology` and
  `Functor.preservesFiniteColimits_of_preservesHomology`.
- `smoothRepToRep_preservesHomology`: smooth representations form a full
  subcategory closed under kernels and cokernels (instances of
  `Langlands.Representation.Category.Abelian`), so its inclusion preserves them
  (Mathlib's `ObjectProperty.preservesKernels_ι` and
  `ObjectProperty.preservesCokernels_ι`).
- `smoothRepExtendScalars_map_exact`: by definition
  `smoothRepExtendScalars R S G ⋙ SmoothRep.toRep` is
  `SmoothRep.toRep ⋙ repExtendScalars R S G`. The inclusion `SmoothRep.toRep` is
  faithful and preserves homology over `R` and over `S`, so the statement
  follows from `repExtendScalars_map_exact` by
  `ShortComplex.exact_map_iff_of_faithful` in both directions.
- The smooth instances are as for `repExtendScalars`.

## Semilinear functors and base-change lifts

Namespace `HyperextScalarExtension`. Section `Lift` takes `[Algebra R S]`, an
`R`-module `M` and an `S`-module `N`. Section `Semilinear` takes an `R`-linear
abelian category `C : Type uC` (`[Category.{vC} C] [Abelian C] [Linear R C]`),
an `S`-linear abelian category `D : Type uD`
(`[Category.{vD} D] [Abelian D] [Linear S D]`) and a functor `F : C ⥤ D`.

| Declaration | Statement |
| --- | --- |
| `baseChangeLift φ hφ` | For an additive map `φ : M →+ N` with `φ (r • m) = algebraMap R S r • φ m`, the `S`-linear map `S ⊗[R] M →ₗ[S] N`. A `def`. |
| `baseChangeLift_tmul` | `baseChangeLift φ hφ (s ⊗ₜ m) = s • φ m` (a `simp` lemma, by definition). |
| `IsSemilinear R S F` | The proposition `∀ X Y (r : R) (f : X ⟶ Y), F.map (r • f) = algebraMap R S r • F.map f`. A `Prop`-valued `def`. |
| `IsSemilinear.map_smul_id F hF r X` | `F.map (r • 𝟙 X) = algebraMap R S r • 𝟙 (F.obj X)`. |

`IsSemilinear R S F` with `S = R` and `algebraMap` the identity says that `F`
is `R`-linear in the sense of Mathlib's `Functor.Linear`; the definition allows
the two categories to be linear over different rings.

Proofs.

- `baseChangeLift`: `N` becomes an `R`-module through `algebraMap R S`
  (`Module.compHom`), with `IsScalarTower R S N`; for this structure `φ` is
  `R`-linear by `hφ`, and the map is Mathlib's `LinearMap.liftBaseChange S`
  applied to it.
- `IsSemilinear.map_smul_id`: `hF` and `F.map (𝟙 X) = 𝟙 (F.obj X)`.

## The comparison maps

Still in section `Semilinear`, now with `[F.Additive]`,
`[PreservesFiniteLimits F]` and `[PreservesFiniteColimits F]`, so that `F` is
exact. Section `Ext` adds instances `HasExt.{t} C` and `HasExt.{t'} D`;
section `Derived` adds instances `HasDerivedCategory.{s} C` and
`HasDerivedCategory.{s'} D`. The `R`- and `S`-linear structures of the derived
categories and the linearity of their single-complex and shift functors are
Mathlib's (`Mathlib.Algebra.Homology.DerivedCategory.Linear`). Here
`hF : IsSemilinear R S F`, `K` is an object of `DerivedCategory C`, `W` an object
of `C`, `n, q : ℤ` (`n : ℕ` for Ext), and `ShiftedHom K W₀ n` is Mathlib's
notation for `K ⟶ W₀⟦n⟧`.

| Declaration | Statement |
| --- | --- |
| `mapExactFunctor_smul F hF r e` | `(r • e).mapExactFunctor F = algebraMap R S r • e.mapExactFunctor F` for `e : Ext^n(X, Y)`, where `Abelian.Ext.mapExactFunctor` is Mathlib's map `Ext^n(X, Y) → Ext^n(F X, F Y)`. |
| `extBaseChangeMap F hF X Y n` | The `S`-linear map `S ⊗[R] Ext^n(X, Y) →ₗ[S] Ext^n(F X, F Y)`, the `baseChangeLift` of Mathlib's `F.mapExtAddHom X Y n`. A `def`; `extBaseChangeMap_tmul` (a `simp` lemma): `s ⊗ e ↦ s • e.mapExactFunctor F`. |
| `abutmentMap F K W n` | The additive map `ShiftedHom K W₀ n →+ ShiftedHom (F K) (F W)₀ n`, `f ↦ f.map F.mapDerivedCategory ≫ (c_W)⟦n⟧'`, where `f.map` is Mathlib's `ShiftedHom.map` (apply `F.mapDerivedCategory` and its commutation with shifts) and `c_W : F(W₀) ≅ (F W)₀` is the component at `W` of Mathlib's `F.mapDerivedCategorySingleFunctor 0`. A `def`; `abutmentMap_apply` states this formula. |
| `abutmentMap_comp_single F K n f g` | Naturality in `W`: for `g : W ⟶ W'`, `abutmentMap F K W' n (f ≫ (g₀)⟦n⟧') = abutmentMap F K W n f ≫ ((F.map g)₀)⟦n⟧'`, where `g₀` is the image of `g` under `DerivedCategory.singleFunctor _ 0`. |
| `comp_single_smul_id W n r f` | In `ShiftedHom X W₀ n`: `f ≫ ((r • 𝟙 W)₀)⟦n⟧' = r • f`. |
| `abutmentMap_smul F hF K W n r f` | `abutmentMap F K W n (r • f) = algebraMap R S r • abutmentMap F K W n f`. |
| `abutmentBaseChangeMap F hF K W n` | The `S`-linear map `S ⊗[R] ShiftedHom K W₀ n →ₗ[S] ShiftedHom (F K) (F W)₀ n`, the `baseChangeLift` of `abutmentMap`. A `def`; `abutmentBaseChangeMap_tmul` (a `simp` lemma): `s ⊗ f ↦ s • abutmentMap F K W n f`. |
| `cohomologyHomMap F K W q` | The additive map `(H^q K ⟶ W) →+ (H^q (F K) ⟶ F W)`, `φ ↦ c_K ≫ F.map φ`, where `c_K : H^q (F K) ≅ F (H^q K)` is the component at `K` of the Library's `exactDerivedHomologyIso F q`. A `def`; `cohomologyHomMap_apply` states this formula. |
| `cohomologyHomMap_smul F hF K W q r φ` | `cohomologyHomMap F K W q (r • φ) = algebraMap R S r • cohomologyHomMap F K W q φ`. |
| `cohomologyHomBaseChangeMap F hF K W q` | The `S`-linear map `S ⊗[R] (H^q K ⟶ W) →ₗ[S] (H^q (F K) ⟶ F W)`, the `baseChangeLift` of `cohomologyHomMap`. A `def`; `cohomologyHomBaseChangeMap_tmul` (a `simp` lemma): `s ⊗ φ ↦ s • cohomologyHomMap F K W q φ`. |

Mathlib's `Functor.mapExtLinearMap R` is the analogue of `extBaseChangeMap` for
a functor that is linear over one ring `R` acting on both categories; it does
not apply when the target category is linear over a different ring `S`.

Proofs.

- `mapExactFunctor_smul`: `r • e = e ∘ mk₀ (r • 𝟙 Y)` (Mathlib's
  `Abelian.Ext.smul_eq_comp_mk₀`); `Abelian.Ext.mapExactFunctor` is compatible
  with composition and sends `mk₀ g` to `mk₀ (F.map g)`
  (`Abelian.Ext.mapExactFunctor_comp`, `Abelian.Ext.mapExactFunctor_mk₀`);
  then `IsSemilinear.map_smul_id` and `Abelian.Ext.smul_eq_comp_mk₀` over `S`.
- `abutmentMap`: additivity of `ShiftedHom.map` and of composition.
- `abutmentMap_comp_single`: the naturality square of
  `F.mapDerivedCategorySingleFunctor 0` at `g`, shifted by `n`, together with
  the naturality of the commutation isomorphism of `F.mapDerivedCategory` with
  the shift (`Functor.commShiftIso_hom_naturality_assoc`).
- `comp_single_smul_id`: the single-complex functor and the shift functor are
  `R`-linear (Mathlib instances), so `((r • 𝟙 W)₀)⟦n⟧' = r • 𝟙`, and
  `Linear.comp_smul`.
- `abutmentMap_smul`: write `r • f` as `f ≫ ((r • 𝟙 W)₀)⟦n⟧'`
  (`comp_single_smul_id` in `C`), apply `abutmentMap_comp_single`, then
  `F.map (r • 𝟙 W) = algebraMap R S r • 𝟙` (`IsSemilinear.map_smul_id`) and
  `comp_single_smul_id` in `D` over `S`.
- `cohomologyHomMap_smul`: `hF` and `Linear.comp_smul`.
- The three base-change maps are `baseChangeLift` applied to the additive maps
  and their semilinearity lemmas.

## Extension of scalars of representations

Section `Rep` takes `[Algebra R S]`; the semilinearity lemmas need no flatness.
Section `Smooth` takes `[Module.Flat R S]`, a topological group `G : Type uG`,
and instances `HasExt` or `HasDerivedCategory` on
`SmoothRep.{uR, uG, w} R G` and on `SmoothRep.{uS, uG, max uS w} S G`. The
`R`-linear structure of `SmoothRep R G` is the one inherited from `Rep R G`.

| Declaration | Statement |
| --- | --- |
| `repExtendScalars_isSemilinear R S G` | `IsSemilinear R S (repExtendScalars.{w} R S G)`, for a monoid `G`. |
| `smoothRepExtendScalars_isSemilinear R S G` | `IsSemilinear R S (smoothRepExtendScalars.{w} R S G)`, for a topological group `G`. |
| `smoothExtBaseChangeMap R S G X Y n` | `extBaseChangeMap` for `smoothRepExtendScalars R S G`: an `S`-linear map `S ⊗[R] Ext^n(X, Y) → Ext^n(S ⊗[R] X, S ⊗[R] Y)` for smooth representations `X`, `Y`, with `Ext` taken in the categories of smooth representations. A `def`. |
| `smoothAbutmentBaseChangeMap R S G K W n` | `abutmentBaseChangeMap` for `smoothRepExtendScalars R S G`. A `def`. |
| `smoothCohomologyHomBaseChangeMap R S G K W q` | `cohomologyHomBaseChangeMap` for `smoothRepExtendScalars R S G`. A `def`. |

Proofs.

- `repExtendScalars_isSemilinear`: two morphisms of representations are equal
  if their underlying linear maps are (`Rep.hom_ext`,
  `Representation.IntertwiningMap.ext`, `LinearMap.ext`). On a pure tensor,
  `s ⊗ (r • f x) = algebraMap R S r • (s ⊗ f x)` (`TensorProduct.tmul_smul`,
  `algebraMap_smul`); both sides are additive, and `TensorProduct.inductionOn`
  concludes.
- `smoothRepExtendScalars_isSemilinear`: `SmoothRep.toRep` is faithful and
  linear, and `SmoothRep.toRep.map ((smoothRepExtendScalars R S G).map f)` is
  `(repExtendScalars R S G).map (SmoothRep.toRep.map f)` by definition; the
  statement follows from `repExtendScalars_isSemilinear`.
- The smooth comparison maps are the general ones applied to
  `smoothRepExtendScalars R S G`, which is exact by the instances of section
  `SmoothExact` and semilinear by `smoothRepExtendScalars_isSemilinear`.

## Provenance and interpretation

The definitions, statements and proofs are ours, assembled from Mathlib and the
Library. Exactness of extension of scalars along a flat algebra and the
`S`-linear extension `S ⊗[R] M → N` of an `R`-semilinear map are standard.

Worker 13, the first executor of the task, asked Worker 61 for the change of
coefficients from `𝒪` to `L_ℓ` for the complexes and groups of morphisms used
in Harris's spectral sequence, and for the maps induced on the degeneration and
on isotypic parts. This module supplies the first part for a general flat
algebra `R → S`: exactness of extension of scalars and the comparison maps on
`Ext`, on `Hom(K, W₀⟦n⟧)` and on `Hom(H^q K, W)`. Their compatibility with the
edge map, with group actions and with isotypic parts is not treated here.

For this module Worker 61 read the following passages of Harris 1999, in the
rendered scans (the text layer of this scan is unreliable):

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §3, printed p.306 (one-based PDF page 8): for a place `v` of `ℚ`, Harris
  writes "`L_v = L ⊗_ℚ ℚ_v`", where `L = L(ρ)` is the number field over which
  the representation `(ρ, W)` is rational.
- §3, printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring of
  integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in `W(L)`."
- §4, printed p.311 (one-based PDF page 13), Proposition 4.10: "There is a
  spectral sequence of `𝒪`-modules (4.10.1)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, L_ℓ(n - 1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`.
  Here `Ext^i` denotes the i-th derived functor of `Hom` in the category of
  smooth `L_ℓ[GJ]`-modules." Just before, `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ`, the limit
  over `m` of the sheaves attached to `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m`.
- §4, printed p.312 (one-based PDF page 14), end of the proof of
  Proposition 4.10: "In fact, we have proved the stronger (integral)
  statement (4.10.4)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒ H^{i+j}(S̄_{K(N)}, 𝓛̃)`."
  The isomorphism (5.2) on the same page,
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_{K(N)}, W̃)[π]`,
  uses the integral cohomology `H_c(M̆_N, 𝒪(n - 1))` together with the
  `L_ℓ`-coefficient module `𝒜_ℓ(GJ, ρ, H)[π^v]` and the `L_ℓ`-coefficient sheaf
  `W̃`.

Interpretation (explanation only). Harris's spectral sequence exists with
integral coefficients (4.10.4) and with `L_ℓ`-coefficients (4.10.1), and (5.2)
mixes the two. Passing from `𝒪`-coefficients to `L_ℓ`-coefficients is extension
of scalars along `𝒪 → L_ℓ`. Since `L_ℓ = L ⊗_ℚ ℚ_ℓ` is a finite product of
finite extensions of `ℚ_ℓ`, `𝒪` is the product of their rings of integers and
`L_ℓ = 𝒪[1/ℓ]` is a localization of `𝒪`, hence flat over `𝒪`. The module takes
flatness as the hypothesis `[Module.Flat R S]` and proves no flatness of a
particular algebra; with `R = 𝒪` and `S = L_ℓ` its comparison maps are the maps
`L_ℓ ⊗_𝒪 (−) → (−)` induced by extension of scalars on the terms of the
integral and rational spectral sequences.

The comparison maps are in general not isomorphisms, which is why the module
states none. For example, for the trivial group, `R = ℤ`, `S = ℚ`,
`X = ⊕_{k ∈ ℕ} ℤ` and `Y = ℤ`, the degree-`0` map `ℚ ⊗_ℤ Hom(X, Y) → Hom(ℚ ⊗ X, ℚ ⊗ Y)`
is `ℚ ⊗_ℤ ℤ^ℕ → ℚ^ℕ`, which misses `(1, 1/2, 1/3, …)` because every element of
the source has bounded denominators. This example is explanation only and is
not formalized. Whether the maps are isomorphisms in Harris's situation
depends on finiteness properties of the cohomology of the Drinfeld tower and of
`𝒜_ℓ(GJ, ρ, H)`, which are not formalized.

## Scope

- No comparison map is proved to be injective, surjective or bijective.
- The specialization to Harris's situation needs inputs that are not
  formalized here: the identification of `H_c(M̆_N, L_ℓ(n - 1))` with the
  extension of scalars of `H_c(M̆_N, 𝒪(n - 1))`, the relation between
  `𝒜_ℓ(GJ, 𝓛, H)` and `𝒜_ℓ(GJ, ρ, H)`, the comparison of the cohomology of
  `S̄_{K(N)}` with coefficients `𝓛̃` and `W̃`, and the geometric inputs of
  Proposition 4.10, which Worker 13 lists as planned obligations.
- The compatibility of the comparison maps with the edge map
  `HyperextDegeneration.edgeMap`, with group actions and with isotypic parts is
  not stated. In particular, no statement relates the isotypic parts of a
  representation over `R` to those of its extension of scalars to `S`; such a
  relation remains an open obligation.
- The general maps need `F` exact (instances `F.Additive`,
  `PreservesFiniteLimits F`, `PreservesFiniteColimits F`) and semilinear (the
  hypothesis `hF`). `HasExt` and `HasDerivedCategory` are hypotheses; the
  results hold for each such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.306, 307, 311 and 312 (rendered scans) read for this module.

Dependencies: `Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension`,
`Langlands.Cohomology.ExactDerivedHomology`,
`Langlands.Representation.Category.Abelian` and Mathlib's
`Algebra.Homology.DerivedCategory.Ext.Map`,
`Algebra.Homology.DerivedCategory.Linear`,
`Algebra.Homology.ShortComplex.ModuleCat` and `RingTheory.Flat.Basic`, with
Mathlib pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
