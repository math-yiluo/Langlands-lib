# Isotypic parts and multiplicity spaces of hyperext groups and localization

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextHomLocalization`
(`isLocalizedModule_mk_one`, `mk_one_injective_of_isSMulRegular`,
`exists_finset_eq_top_of_finite_asModule`,
`repCohomologyHomBaseChangeMap_bijective_of_isLocalization`,
`smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization`,
`repHom_isSMulRegular`, `smoothRepHom_isSMulRegular`; Worker 61) and
`Langlands.Cohomology.HyperextIsotypicDegenerationBaseChange`
(`intertwiningMapCompLinearMap`, `intertwiningMapComp`,
`abutmentMultiplicityBaseChangeMap`, `cohomologyHomMultiplicityBaseChangeMap`,
`abutmentMultiplicityBaseChangeMap_bijective_iff`,
`abutmentIsotypicBaseChangeMap_bijective_iff`,
`abutmentIsotypicBaseChangeEquiv`,
`abutmentIsotypicProdBaseChangeIntertwiningMap`,
`cohomologyHomIsotypicProdBaseChangeIntertwiningMap`,
`abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_iff`,
`abutmentIsotypicProdBaseChangeEquiv`,
`smoothAbutmentIsotypicBaseChangeMap_bijective_iff`,
`smoothAbutmentIsotypicBaseChangeEquiv`; Worker 61). Through these imports it
also uses `Langlands.Cohomology.HyperextIsotypicBaseChange`
(`baseChangeIntertwiningMap`, `multiplicityBaseChangeMap`,
`multiplicityBaseChangeMap_tmul`, `isotypicBaseChangeMap`,
`coe_isotypicBaseChangeMap`, `isotypicBaseChangeMap_injective`,
`cohomologyHomBaseChangeIntertwiningMap`,
`abutmentIsotypicBaseChangeMap`, `cohomologyHomIsotypicBaseChangeMap`,
`smoothAbutmentIsotypicBaseChangeMap`,
`smoothCohomologyHomIsotypicBaseChangeMap`; Worker 61),
`Langlands.Cohomology.HyperextDegenerationIsotypic` (`isotypicPart`,
`isotypicPart_le_iff`, `apply_mem_isotypicPart`,
`intertwiningMap_apply_mem_isotypicPart`, `isotypicRepresentation`,
`isotypicProdRepresentation`,
`isotypicIntertwiningMap`, `abutmentRepresentation`,
`cohomologyHomRepresentation`; Worker 61),
`Langlands.Cohomology.HyperextScalarExtension` (`IsSemilinear`,
`cohomologyHomBaseChangeMap`, `repExtendScalars_isSemilinear`,
`smoothRepExtendScalars_isSemilinear`; Worker 61) and
`Langlands.Cohomology.DivisibleSystem.ScalarExtension`
(`baseChangeRepresentation`, `baseChangeRepresentation_apply_tmul`,
`repExtendScalars`; Worker 61), and `smoothRepExtendScalars` of
`Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension` (Worker 61).

Let `S` be the localization of a commutative ring `R` at a submonoid `M`. For
representations `τ` and `ρ` of a group `Γ` over `R`, the Library's
`multiplicityBaseChangeMap S τ ρ` and `isotypicBaseChangeMap S τ ρ` compare
the multiplicity space `Hom_Γ(τ, ρ)` and the `τ`-isotypic part of `ρ` with the
corresponding objects for `S ⊗[R] τ` and `S ⊗[R] ρ`; the Library proves the
second injective for flat `S` and neither surjective. This module proves both
bijective when `τ` is finitely generated over the group algebra `R[Γ]` and `ρ`
has no `M`-torsion. With the Library's reduction of the abutment maps to the
maps on `Hom(H^{-n} K, W)` (`HyperextIsotypicDegenerationBaseChange`) and the
bijectivity of the map on `Hom(H^{-n} K, W)` (`HyperextHomLocalization`), it
derives the bijectivity of the base-change maps on multiplicity spaces and
isotypic parts of the hyperext groups `Hom(H^{-n} K, W)` and `Hom(K, W₀⟦n⟧)`.
The finiteness, torsion and degeneration hypotheses remain explicit.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`
and use the Library's `HyperextAbutment` namespace (`open HyperextAbutment`).
For a representation `ρ` of `Γ` over `R` on `V`, `S ⊗[R] ρ` below denotes the
Library's `baseChangeRepresentation S ρ`, the representation on `S ⊗[R] V` in
which `γ` acts by `(ρ γ).baseChange S`; `Hom_Γ(τ, ρ)` denotes Mathlib's
`τ.IntertwiningMap ρ` and `ρ[τ]` the Library's `isotypicPart τ ρ`, the sum of
the images of all intertwining maps `τ → ρ`. "`V` has no `M`-torsion" means
`∀ m : M, IsSMulRegular V (m : R)`, and "`τ` is finitely generated over
`R[Γ]`" is the instance `[Module.Finite (MonoidAlgebra R Γ) τ.asModule]`.

## Bijective intertwining maps

Section `Bijective` takes a commutative ring `R`, a group `Γ` and
representations `τ`, `ρ`, `σ` of `Γ` over `R` on `U`, `V`, `W`.

| Declaration | Statement |
| --- | --- |
| `intertwiningMapCompLinearMap_bijective τ φ hφ` | For `φ : ρ.IntertwiningMap σ` with `hφ : Function.Bijective φ`: the Library's `intertwiningMapCompLinearMap τ φ : Hom_Γ(τ, ρ) → Hom_Γ(τ, σ)`, `f ↦ φ ∘ f`, is bijective. |
| `isotypicIntertwiningMap_bijective τ φ hφ` | Under the same hypotheses, the Library's restriction `isotypicIntertwiningMap τ φ : ρ[τ] → σ[τ]` is bijective. |

Proofs. Injectivity is that of `φ`. For surjectivity let `e` be the
equivalence of representations of Mathlib's
`Representation.IntertwiningMap.ofBijective φ hφ`. An intertwining map
`g : τ → σ` is `φ ∘ (e⁻¹ ∘ g)`; an element `y` of `σ[τ]` is `φ (e⁻¹ y)`, and
`e⁻¹ y` lies in `ρ[τ]` because intertwining maps send isotypic parts into
isotypic parts (the Library's `intertwiningMap_apply_mem_isotypicPart`).

## Multiplicity spaces and isotypic parts under localization

Section `Algebra` takes commutative rings `R : Type uR`, `S : Type uS` with
`[Algebra R S]`, a submonoid `M : Submonoid R` with `[IsLocalization M S]`
(`S` and `M` explicit), a group `Γ : Type uΓ`, representations `τ` on `U` and
`ρ` on `V` over `R`, and `hV : ∀ m : M, IsSMulRegular V (m : R)`.

| Declaration | Statement |
| --- | --- |
| `multiplicityBaseChangeMap_injective S M hV` | `multiplicityBaseChangeMap S τ ρ : S ⊗[R] Hom_Γ(τ, ρ) → Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)` is injective. |
| `multiplicityBaseChangeMap_surjective S M hV` | If `τ` is finitely generated over `R[Γ]`, `multiplicityBaseChangeMap S τ ρ` is surjective. |
| `multiplicityBaseChangeMap_bijective S M hV` | If `τ` is finitely generated over `R[Γ]`, `multiplicityBaseChangeMap S τ ρ` is bijective. |
| `multiplicityBaseChangeEquiv S M hV` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Hom_Γ(τ, ρ) ≃ₗ[S] Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)` with underlying map `multiplicityBaseChangeMap S τ ρ`. A `def`. |
| `multiplicityBaseChangeEquiv_apply S M hV x` | Its value at `x` is `multiplicityBaseChangeMap S τ ρ x` (a `simp` lemma, by definition). |
| `isotypicBaseChangeMap_surjective_of_finite S M τ hV` | If `τ` is finitely generated over `R[Γ]`, `isotypicBaseChangeMap S τ ρ : S ⊗[R] ρ[τ] → (S ⊗[R] ρ)[S ⊗[R] τ]` is surjective. |
| `isotypicBaseChangeMap_bijective_of_finite S M τ hV` | Under the same hypotheses, `isotypicBaseChangeMap S τ ρ` is bijective. |
| `isotypicBaseChangeEquivOfFinite S M τ hV` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] ρ[τ] ≃ₗ[S] (S ⊗[R] ρ)[S ⊗[R] τ]` with underlying map `isotypicBaseChangeMap S τ ρ`. A `def`. |
| `isotypicBaseChangeEquivOfFinite_apply S M τ hV x` | Its value at `x` is `isotypicBaseChangeMap S τ ρ x` (a `simp` lemma, by definition). |

Proofs. The first three follow the proofs of the Library's
`repHomBaseChangeMap_injective` and `repHomBaseChangeMap_surjective`, with
intertwining maps of representations on arbitrary modules in place of morphisms
in `Rep`.

- `multiplicityBaseChangeMap_injective`: `S ⊗[R] Hom_Γ(τ, ρ)` is the
  localization of `Hom_Γ(τ, ρ)` at `M` (the Library's
  `isLocalizedModule_mk_one`), so for `t` in the kernel, `m • t = 1 ⊗ φ` for
  some `m ∈ M` and `φ : Hom_Γ(τ, ρ)`. Applying the map gives
  `φ.baseChange S = 0`, so `1 ⊗ φ u = 0` and hence `φ u = 0` for every `u`
  (the Library's `mk_one_injective_of_isSMulRegular`). Hence `m • t = 0`, and
  `t = 0` because the image of `m` is a unit of `S`.
- `multiplicityBaseChangeMap_surjective`: let
  `g : Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)` and let `t` be the finite set of the
  Library's `exists_finset_eq_top_of_finite_asModule τ`. There is one `b ∈ M`
  such that `b • g (1 ⊗ u)` lies in the image of `v ↦ 1 ⊗ v` for every `u ∈ t`
  (Mathlib's `IsLocalizedModule.exist_integer_multiples`). The `R`-linear map
  `L : U → S ⊗[R] V`, `u ↦ b • g (1 ⊗ u)`, is `Γ`-equivariant, so the set of
  `u` with `L u` in this image is a `Γ`-stable `R`-submodule containing `t`,
  hence all of `U`. By injectivity of `v ↦ 1 ⊗ v`, `L = (v ↦ 1 ⊗ v) ∘ f` for a
  unique `R`-linear `f : U → V`, which is `Γ`-equivariant by the same
  injectivity. With `a = IsLocalization.mk' S 1 b`, the intertwining map
  `a • f.baseChange S` agrees with `g` on every `s ⊗ u`; both are additive, so
  `multiplicityBaseChangeMap S τ ρ (a ⊗ f) = g`.
- `multiplicityBaseChangeMap_bijective`, `multiplicityBaseChangeEquiv`: the two
  previous theorems and Mathlib's `LinearEquiv.ofBijective`.
- `isotypicBaseChangeMap_surjective_of_finite`: the underlying map of
  `isotypicBaseChangeMap S τ ρ` is the base change of the inclusion
  `ρ[τ] → V` (the Library's `coe_isotypicBaseChangeMap`); let `N` be the range
  of this base change. By the Library's `isotypicPart_le_iff`, it suffices that
  `g z ∈ N` for every `g : Hom_Γ(S ⊗[R] τ, S ⊗[R] ρ)` and `z : S ⊗[R] U`. By
  `multiplicityBaseChangeMap_surjective`, `g` is the image of some
  `t : S ⊗[R] Hom_Γ(τ, ρ)`; by additivity in `t` and in `z` it suffices to take
  `t = s ⊗ f` and `z = s' ⊗ u`, where `g z = (s s') ⊗ f u` is the image of
  `(s s') ⊗ f u` with `f u ∈ ρ[τ]` (the Library's `apply_mem_isotypicPart`).
- `isotypicBaseChangeMap_bijective_of_finite`: `S` is flat over `R` (Mathlib's
  `IsLocalization.flat`), so injectivity is the Library's
  `isotypicBaseChangeMap_injective`; surjectivity is the previous theorem.
- `isotypicBaseChangeEquivOfFinite`: Mathlib's `LinearEquiv.ofBijective`.

## Hyperext groups

Section `Derived` takes `R`, `S` (implicit) and `M` (explicit) as above, an
`R`-linear abelian category `C : Type uC` (`[Category.{vC} C] [Abelian C]
[Linear R C]`, `[HasDerivedCategory.{s} C]`), an `S`-linear abelian category
`D : Type uD` (`[Category.{vD} D] [Abelian D] [Linear S D]`,
`[HasDerivedCategory.{s'} D]`), a functor `F : C ⥤ D` with `[F.Additive]`,
`[PreservesFiniteLimits F]` and `[PreservesFiniteColimits F]`,
`hF : IsSemilinear R S F`, groups `Γ : Type uΓ` and `Δ : Type uΔ`, and an
`R`-module `U`. Below
`K` is an object of `DerivedCategory C`, `W` an object of `C` with `W₀` the
complex `W` placed in degree `0`, `n : ℤ`, `H^i K = (homologyFunctor C i).obj K`,
`ρ : Γ →* Aut K`, `σ : Γ →* Aut W`, and `τ : Representation R Γ U` is finitely
generated over `R[Γ]`. Write `F K` for `F.mapDerivedCategory.obj K`,
`ρ_F = (F.mapDerivedCategory.mapAut K).comp ρ` and `σ_F = (F.mapAut W).comp σ`.
In the three `…Prod…` declarations, `ρ : Γ × Δ →* Aut K` and
`σ : Γ × Δ →* Aut W` instead, and the isotypic parts are those for `Γ` of the
restrictions along `MonoidHom.inl Γ Δ`, with `Δ` acting on them (the Library's
`isotypicProdRepresentation`).
The two hypotheses on `Hom(H^{-n} K, W)` are
`hreg : ∀ m : M, IsSMulRegular (H^{-n} K ⟶ W) (m : R)` and
`h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))`.

From `abutmentMultiplicityBaseChangeMap_bijective_of_isSMulRegular` on the
section also takes `[HasExt.{t} C]` and `[HasExt.{t'} D]`, and the degeneration
hypotheses of `HyperextIsotypicDegenerationBaseChange`: `b : ℤ`,
`hK : ∀ i > b, IsZero (H^i K)`,
`hW : ∀ k, ∀ i > 0, Subsingleton (Ext^i(H^k K, W))` (`Abelian.Ext.{t}`) and
`hW' : ∀ k, ∀ i > 0, Subsingleton (Ext^i(H^k (F K), F W))` (`Abelian.Ext.{t'}`).

| Declaration | Statement |
| --- | --- |
| `cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular M F hF ρ σ n τ hreg h` | `cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ : S ⊗[R] Hom_Γ(τ, cohomologyHomRepresentation R ρ σ n) → Hom_Γ(S ⊗[R] τ, cohomologyHomRepresentation S ρ_F σ_F n)` is bijective. |
| `cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular M F hF ρ σ n τ hreg h` | `cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ : S ⊗[R] (cohomologyHomRepresentation R ρ σ n)[τ] → (cohomologyHomRepresentation S ρ_F σ_F n)[S ⊗[R] τ]` is bijective. |
| `abutmentMultiplicityBaseChangeMap_bijective_of_isSMulRegular M F hF b hK hW hW' n ρ σ τ hreg h` | Under the degeneration hypotheses, `abutmentMultiplicityBaseChangeMap F hF ρ σ n τ` is bijective. |
| `abutmentMultiplicityLocalizationEquivOfIsSMulRegular M F hF b hK hW hW' n ρ σ τ hreg h` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Hom_Γ(τ, abutmentRepresentation R ρ σ n) ≃ₗ[S] Hom_Γ(S ⊗[R] τ, abutmentRepresentation S ρ_F σ_F n)` with underlying map `abutmentMultiplicityBaseChangeMap F hF ρ σ n τ`. A `def`. |
| `abutmentIsotypicBaseChangeMap_bijective_of_isSMulRegular M F hF b hK hW hW' n ρ σ τ hreg h` | Under the degeneration hypotheses, `abutmentIsotypicBaseChangeMap F hF ρ σ n τ` is bijective. |
| `abutmentIsotypicLocalizationEquivOfIsSMulRegular M F hF b hK hW hW' n ρ σ τ hreg h` | Under the same hypotheses, the Library's `abutmentIsotypicBaseChangeEquiv F hF b hK hW hW' n ρ σ τ` applied to the bijectivity of `cohomologyHomIsotypicBaseChangeMap`: an equivalence of representations of `Γ` from `S ⊗[R]` the representation on `(abutmentRepresentation R ρ σ n)[τ]` to the representation on `(abutmentRepresentation S ρ_F σ_F n)[S ⊗[R] τ]` (`isotypicRepresentation`). A `def`. |
| `cohomologyHomIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular M F hF ρ σ n τ hreg h` | For actions of `Γ × Δ`: the Library's `cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ`, the intertwining map of representations of `Δ` with underlying map the base-change map on `τ`-isotypic parts for `Γ` of `Hom(H^{-n} K, W)`, is bijective. |
| `abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular M F hF b hK hW hW' n ρ σ τ hreg h` | For actions of `Γ × Δ`, under the degeneration hypotheses: the Library's `abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ` is bijective. |
| `abutmentIsotypicProdLocalizationEquivOfIsSMulRegular M F hF b hK hW hW' n ρ σ τ hreg h` | Under the same hypotheses, the Library's `abutmentIsotypicProdBaseChangeEquiv F hF b hK hW hW' n ρ σ τ` applied to the previous bijectivity of `cohomologyHomIsotypicProdBaseChangeIntertwiningMap`: an equivalence of representations of `Δ`. A `def`. |

Proofs.

- `cohomologyHomMultiplicityBaseChangeMap_bijective_of_isSMulRegular`: by
  definition, `cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ` is
  `multiplicityBaseChangeMap S τ (cohomologyHomRepresentation R ρ σ n)`
  followed by `intertwiningMapCompLinearMap` of the Library's
  `cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n`, whose underlying map is
  `cohomologyHomBaseChangeMap F hF K W (-n)`. The representation
  `cohomologyHomRepresentation R ρ σ n` acts on `H^{-n} K ⟶ W`, so the first
  factor is bijective by `multiplicityBaseChangeMap_bijective` and `hreg`, the
  second by `intertwiningMapCompLinearMap_bijective` and `h`.
- `cohomologyHomIsotypicBaseChangeMap_bijective_of_isSMulRegular`: likewise,
  `cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ` is
  `isotypicBaseChangeMap S τ (cohomologyHomRepresentation R ρ σ n)` followed by
  `isotypicIntertwiningMap` of `cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n`;
  use `isotypicBaseChangeMap_bijective_of_finite` and
  `isotypicIntertwiningMap_bijective`.
- `cohomologyHomIsotypicProdBaseChangeIntertwiningMap_bijective_of_isSMulRegular`:
  by definition its underlying map is
  `isotypicBaseChangeMap S τ ((cohomologyHomRepresentation R ρ σ n).comp (MonoidHom.inl Γ Δ))`
  followed by `isotypicIntertwiningMap` of the restriction along
  `MonoidHom.inl Γ Δ` (the Library's `intertwiningMapComp`) of
  `cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n`; use
  `isotypicBaseChangeMap_bijective_of_finite` and
  `isotypicIntertwiningMap_bijective`.
- The abutment theorems: the Library's
  `abutmentMultiplicityBaseChangeMap_bijective_iff`,
  `abutmentIsotypicBaseChangeMap_bijective_iff` and
  `abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_iff` reduce them to
  the corresponding theorems for `Hom(H^{-n} K, W)`.
- `abutmentMultiplicityLocalizationEquivOfIsSMulRegular`: Mathlib's
  `LinearEquiv.ofBijective`; `abutmentIsotypicLocalizationEquivOfIsSMulRegular`:
  the Library's `abutmentIsotypicBaseChangeEquiv` with the bijectivity of
  `cohomologyHomIsotypicBaseChangeMap` proved above;
  `abutmentIsotypicProdLocalizationEquivOfIsSMulRegular`: likewise with the
  Library's `abutmentIsotypicProdBaseChangeEquiv`.

## Representations and smooth representations

Section `Rep` takes `R : Type uR` and `S : Type uS` with `[Algebra R S]`,
`[Module.Flat R S]`, `M : Submonoid R` with `[IsLocalization M S]`, a monoid
`G : Type uG` (`R`, `S`, `M` and `G` explicit), instances
`HasDerivedCategory.{s}` on `Rep.{w} R G` and `HasDerivedCategory.{s'}` on
`Rep.{max uS w} S G`, a group `Γ : Type uΓ` and an `R`-module `U`; the abutment
declarations also take `HasExt.{t}` and `HasExt.{t'}` instances on these
categories. `K`, `W`, `ρ`, `σ`, `n`, `τ`, `b`, `hK`, `hW`, `hW'` are as above
with `C` the category `Rep.{w} R G` and `F` the Library's extension of scalars
`E = repExtendScalars.{w} R S G`, `hF = repExtendScalars_isSemilinear.{w} R S G`.
Every declaration takes
`[Module.Finite (MonoidAlgebra R G) (H^{-n} K).ρ.asModule]` (finite generation
of `H^{-n} K` over `R[G]`), `[Module.Finite (MonoidAlgebra R Γ) τ.asModule]`
and `hreg : ∀ m : M, IsSMulRegular W (m : R)`; the two `…Prod…` declarations
also take a group `Δ : Type uΔ`, with `ρ : Γ × Δ →* Aut K` and
`σ : Γ × Δ →* Aut W`. The flatness instance holds for
every localization (Mathlib's `IsLocalization.flat`) and is a separate argument
because the Library derives the exactness instances of `E` from it.

Section `Smooth` takes the same data with a topological group `G : Type uG`
(`[Group G] [TopologicalSpace G]`), the categories
`SmoothRep.{uR, uG, w} R G` and `SmoothRep.{uS, uG, max uS w} S G` of smooth
representations, `F` the Library's
`E' = smoothRepExtendScalars.{w} R S G` with
`hF = smoothRepExtendScalars_isSemilinear.{w} R S G`, and finite generation
over `R[G]` of the underlying representation of `H^{-n} K`,
`[Module.Finite (MonoidAlgebra R G) (H^{-n} K).obj.ρ.asModule]`.

| Declaration | Statement |
| --- | --- |
| `repCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg` | `cohomologyHomMultiplicityBaseChangeMap E hF ρ σ n τ` is bijective. |
| `repCohomologyHomIsotypicBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg` | `cohomologyHomIsotypicBaseChangeMap E hF ρ σ n τ` is bijective. |
| `repAbutmentMultiplicityBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg` | Under the degeneration hypotheses, `abutmentMultiplicityBaseChangeMap E hF ρ σ n τ` is bijective. |
| `repAbutmentIsotypicBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg` | Under the degeneration hypotheses, `abutmentIsotypicBaseChangeMap E hF ρ σ n τ` is bijective. |
| `repAbutmentMultiplicityLocalizationEquiv R S M G b hK hW hW' n ρ σ τ hreg` | `abutmentMultiplicityBaseChangeMap E hF ρ σ n τ` as an `S`-linear equivalence. A `def`. |
| `repAbutmentIsotypicLocalizationEquiv R S M G b hK hW hW' n ρ σ τ hreg` | The Library's `abutmentIsotypicBaseChangeEquiv` for `E`, an equivalence of representations of `Γ` with underlying map `abutmentIsotypicBaseChangeMap E hF ρ σ n τ`. A `def`. |
| `repAbutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg` | For actions of `Γ × Δ`, under the degeneration hypotheses: `abutmentIsotypicProdBaseChangeIntertwiningMap E hF ρ σ n τ` is bijective. |
| `repAbutmentIsotypicProdLocalizationEquiv R S M G b hK hW hW' n ρ σ τ hreg` | Under the same hypotheses, the Library's `abutmentIsotypicProdBaseChangeEquiv` for `E`, an equivalence of representations of `Δ`. A `def`. |
| `smoothCohomologyHomMultiplicityBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg` | `cohomologyHomMultiplicityBaseChangeMap E' hF ρ σ n τ` is bijective. |
| `smoothCohomologyHomIsotypicBaseChangeMap_bijective_of_finite R S M G ρ σ n τ hreg` | The Library's `smoothCohomologyHomIsotypicBaseChangeMap R S G ρ σ n τ` is bijective. |
| `smoothAbutmentMultiplicityBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg` | Under the degeneration hypotheses, `abutmentMultiplicityBaseChangeMap E' hF ρ σ n τ` is bijective. |
| `smoothAbutmentIsotypicBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg` | Under the degeneration hypotheses, the Library's `smoothAbutmentIsotypicBaseChangeMap R S G ρ σ n τ` is bijective. |
| `smoothAbutmentMultiplicityLocalizationEquiv R S M G b hK hW hW' n ρ σ τ hreg` | `abutmentMultiplicityBaseChangeMap E' hF ρ σ n τ` as an `S`-linear equivalence. A `def`. |
| `smoothAbutmentIsotypicLocalizationEquiv R S M G b hK hW hW' n ρ σ τ hreg` | The Library's `smoothAbutmentIsotypicBaseChangeEquiv`, an equivalence of representations of `Γ` with underlying map `smoothAbutmentIsotypicBaseChangeMap R S G ρ σ n τ`. A `def`. |
| `smoothAbutmentIsotypicProdBaseChangeIntertwiningMap_bijective_of_finite R S M G b hK hW hW' n ρ σ τ hreg` | For actions of `Γ × Δ`, under the degeneration hypotheses: `abutmentIsotypicProdBaseChangeIntertwiningMap E' hF ρ σ n τ` is bijective. |
| `smoothAbutmentIsotypicProdLocalizationEquiv R S M G b hK hW hW' n ρ σ τ hreg` | Under the same hypotheses, the Library's `abutmentIsotypicProdBaseChangeEquiv` for `E'`, an equivalence of representations of `Δ`. A `def`. |

Proofs. The results of section `Derived` for `F = E` (resp. `E'`), with `hreg`
for `H^{-n} K ⟶ W` from the Library's `repHom_isSMulRegular` (resp.
`smoothRepHom_isSMulRegular`) and `h` from the Library's
`repCohomologyHomBaseChangeMap_bijective_of_isLocalization` (resp.
`smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization`) for `q = -n`.
The Library's smooth maps, `smoothAbutmentIsotypicBaseChangeMap_bijective_iff`
and `smoothAbutmentIsotypicBaseChangeEquiv` are by definition the general ones
for `E'`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. `HyperextIsotypicBaseChange` defines the base-change maps on isotypic
parts and multiplicity spaces and `HyperextIsotypicDegenerationBaseChange`
reduces their bijectivity for the abutment to that for `Hom(H^{-n} K, W)`; the
Scope section of `Langlands.Cohomology.HyperextInvariantsLocalization`, which
treats `Γ`-invariants, leaves isotypic parts and multiplicity spaces open. This
module treats them for finitely generated `τ`.

The passages of Harris 1999 behind this module are those quoted, from the
rendered scans, in the Markdown files of
`Langlands.Cohomology.HyperextScalarExtension`,
`Langlands.Cohomology.HyperextInvariantsLocalization` and
`Langlands.Cohomology.HyperextHomLocalization`:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §3, printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring of
  integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in `W(L)`."
- §5, printed p.312 (one-based PDF page 14): "the spectral sequence (4.10.1)
  degenerates to an isomorphism (5.2)
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_{K(N)}, W̃)[π]`".

Interpretation (explanation only). As explained in the Markdown file of
`HyperextScalarExtension`, `L_ℓ = 𝒪[1/ℓ]` is a localization of `𝒪` (at the
powers of `ℓ`); the formalization does not construct this `IsLocalization`
instance. The left side of (5.2) is a part of a Hom group out of integral
cohomology cut out by a representation (`[JL(π_v)]`), and its right side
mixes integral and `L_ℓ`-coefficient objects. This module shows that, for the
degeneration of `HyperextIsotypicDegenerationBaseChange`, isotypic parts and
multiplicity spaces for a representation `τ` over `𝒪` that is finitely
generated over `𝒪[Γ]` are compatible with passing from `𝒪` to `L_ℓ`, when
`H^{-n} K` is finitely generated over `𝒪[G]` and `W` has no `ℓ`-torsion. The
module does not identify `G`, `Γ`, `τ`, `K` or `W` with Harris's objects, and
whether the finiteness, torsion and degeneration hypotheses hold in his
situation is not addressed.

## Scope

- Finite generation of `τ` over `R[Γ]` and of `H^{-n} K` over `R[G]`, the
  absence of `M`-torsion in `W` (or, in section `Derived`, in
  `Hom(H^{-n} K, W)`), the bijectivity hypothesis `h` of section `Derived` and
  the degeneration hypotheses are not verified for any complex; whether they
  hold in Harris's situation remains an open obligation.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.307 and 312 (rendered scans) as quoted in
`Langlands.Cohomology.HyperextScalarExtension`,
`Langlands.Cohomology.HyperextInvariantsLocalization` and
`Langlands.Cohomology.HyperextHomLocalization`.

Dependencies: `Langlands.Cohomology.HyperextHomLocalization` and
`Langlands.Cohomology.HyperextIsotypicDegenerationBaseChange`, with Mathlib
pinned to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
