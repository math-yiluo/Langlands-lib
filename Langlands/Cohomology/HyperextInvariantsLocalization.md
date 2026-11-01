# Invariants of hyperext groups and localization

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextIsotypicDegenerationBaseChange`
(`invariantsLinearMap`, `abutmentInvariantsBaseChangeMap`,
`cohomologyHomInvariantsBaseChangeMap`,
`abutmentInvariantsBaseChangeMap_bijective_iff` and the smooth maps
`smoothAbutmentInvariantsBaseChangeMap`,
`smoothCohomologyHomInvariantsBaseChangeMap`; Worker 61) and
`Langlands.Representation.Smooth.Definitions` (`IsSmooth`). Through these
imports it also uses `Langlands.Cohomology.HyperextIsotypicBaseChange`
(`invariantsBaseChangeMap`, `invariantsBaseChangeMap_injective`,
`abutmentBaseChangeIntertwiningMap`, `cohomologyHomBaseChangeIntertwiningMap`;
Worker 61), `Langlands.Cohomology.HyperextScalarExtension` (`IsSemilinear`,
`abutmentBaseChangeMap`, `cohomologyHomBaseChangeMap`,
`smoothCohomologyHomBaseChangeMap`, `smoothRepExtendScalars_isSemilinear`;
Worker 61), `Langlands.Cohomology.HyperextDegenerationIsotypic`
(`abutmentRepresentation`, `cohomologyHomRepresentation`; Worker 61) and
`baseChangeRepresentation` of
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (Worker 61). From
Mathlib it imports `Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Localization.BaseChange`.

Let `S` be the localization of a commutative ring `R` at a submonoid `M`. For a
representation `ρ` of a group `Γ` over `R` on `V`, the Library's
`invariantsBaseChangeMap S ρ : S ⊗[R] ρ^Γ → (S ⊗[R] ρ)^Γ` is injective because
`S` is flat over `R`, but it need not be surjective (see Scope). This module
proves that it is bijective when every orbit of `Γ` in `V` is finite, and
applies this to the base-change maps on `Γ`-invariants of the hyperext groups
`Hom(K, W₀⟦n⟧)` and `Hom(H^{-n} K, W)` defined in
`HyperextIsotypicDegenerationBaseChange`. The finite-orbit hypotheses, and the
bijectivity of the base-change maps before taking invariants, remain explicit
hypotheses.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`
and use the Library's `HyperextAbutment` namespace (`open HyperextAbutment`).
For a representation `ρ` of `Γ` over `R` on `V`, `S ⊗[R] ρ` below denotes the
Library's `baseChangeRepresentation S ρ`, the representation on `S ⊗[R] V` in
which `γ` acts by `(ρ γ).baseChange S`, and `ρ^Γ` denotes Mathlib's
`ρ.invariants`.

## Finite orbits and localization

Section `Algebra` takes a commutative ring `R : Type uR`, a group
`Γ : Type uΓ`, and `R`-modules `V`, `W`; from
`invariantsBaseChangeMap_surjective_of_isLocalization` on also a commutative
ring `S : Type uS` with `[Algebra R S]` and a submonoid `M : Submonoid R` with
`[IsLocalization M S]` (both `S` and `M` explicit).

| Declaration | Statement |
| --- | --- |
| `HasFiniteOrbits ρ` | For `ρ : Representation R Γ V`: for every `v : V`, the orbit `Set.range fun γ : Γ => ρ γ v` is finite. A `def` (a `Prop`). |
| `hasFiniteOrbits_of_finite ρ` | If `[Finite Γ]`, every `ρ : Representation R Γ V` satisfies `HasFiniteOrbits ρ`. |
| `hasFiniteOrbits_comp_subtype_of_isSmooth hρ K` | For a topological group `G : Type uG` (`[TopologicalSpace G] [IsTopologicalGroup G]`), a representation `ρ : Representation R G V` with `hρ : IsSmooth ρ` (every vector is fixed by some open subgroup), and a subgroup `K : Subgroup G` with `[CompactSpace K]`: `HasFiniteOrbits (ρ.comp K.subtype)`. |
| `invariantsLinearMap_bijective φ hφ` | For representations `ρ`, `σ` of `Γ` on `V`, `W` and an intertwining map `φ : ρ.IntertwiningMap σ` with `hφ : Function.Bijective φ`: `invariantsLinearMap φ : ρ^Γ →ₗ[R] σ^Γ` is bijective. |
| `invariantsBaseChangeMap_surjective_of_isLocalization S M hρ` | For `ρ : Representation R Γ V` with `hρ : HasFiniteOrbits ρ`: `invariantsBaseChangeMap S ρ` is surjective. |
| `invariantsBaseChangeMap_bijective_of_isLocalization S M hρ` | Under the same hypotheses, `invariantsBaseChangeMap S ρ` is bijective. |
| `invariantsBaseChangeEquivOfIsLocalization S M hρ` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] ρ^Γ ≃ₗ[S] (S ⊗[R] ρ)^Γ` with underlying map `invariantsBaseChangeMap S ρ`. A `def`. |
| `invariantsBaseChangeEquivOfIsLocalization_apply S M hρ x` | Its value at `x` is `invariantsBaseChangeMap S ρ x` (a `simp` lemma, by definition). |

Proofs.

- `hasFiniteOrbits_of_finite`: the range of a function on a finite type is
  finite (Mathlib's `Set.finite_range`).
- `hasFiniteOrbits_comp_subtype_of_isSmooth`: for `v : V`, smoothness gives an
  open subgroup `U` of `G` fixing `v`. Its trace `H = U ∩ K` (Mathlib's
  `Subgroup.subgroupOf`) is an open subgroup of the compact group `K`, so
  `K ⧸ H` is finite (Mathlib's `Subgroup.quotient_finite_of_isOpen`). Every
  `k : K` is `k = q h` with `q` the chosen representative of the coset of `k`
  and `h ∈ H` (Mathlib's `QuotientGroup.mk_out_eq_mul`), and `ρ h v = v`, so the
  orbit of `v` is contained in the image of the finite set `K ⧸ H` under
  `q ↦ ρ q v`.
- `invariantsLinearMap_bijective`: injectivity is that of `φ`. For
  surjectivity, an invariant `w` is `φ v` for some `v : V`, and `v` is
  invariant because `φ (ρ γ v) = σ γ (φ v) = φ v` and `φ` is injective.
- `invariantsBaseChangeMap_surjective_of_isLocalization`: since `S ⊗[R] V` is
  the localization of `V` at `M` (Mathlib's `isLocalizedModule_iff_isBaseChange`
  and `TensorProduct.isBaseChange`), an invariant `x : S ⊗[R] V` satisfies
  `m • x = 1 ⊗ₜ v` for some `m ∈ M` and `v : V`
  (Mathlib's `IsLocalizedModule.surj`). For each `γ`, invariance of `x` gives
  `1 ⊗ₜ ρ γ v = 1 ⊗ₜ v`, hence some `c_γ ∈ M` with `c_γ • (ρ γ v - v) = 0`
  (Mathlib's `IsLocalizedModule.eq_zero_iff`). Choosing one `c_w ∈ M` for each
  point `w = ρ γ v` of the finite orbit of `v` and letting `P ∈ M` be their
  product, `P • ρ γ v = P • v` for every `γ`, so `P • v` is invariant. With
  `u = IsLocalization.mk' S 1 (m P)` (so `u · (m P) = 1` in `S`),
  `x = u ⊗ₜ (P • v)`, which is the image of the element `u ⊗ₜ (P • v)` of
  `S ⊗[R] ρ^Γ`.
- `invariantsBaseChangeMap_bijective_of_isLocalization`: `S` is flat over `R`
  (Mathlib's `IsLocalization.flat`), so injectivity is the Library's
  `invariantsBaseChangeMap_injective`; surjectivity is the previous theorem.
- `invariantsBaseChangeEquivOfIsLocalization`: Mathlib's
  `LinearEquiv.ofBijective` applied to the previous theorem.

## Hyperext groups

Section `Derived` takes `R`, `S` and `M` as above (`M` explicit, `S` implicit),
an `R`-linear abelian category `C : Type uC` (`[Category.{vC} C] [Abelian C]
[Linear R C]`, `[HasDerivedCategory.{s} C]`), an `S`-linear abelian category
`D : Type uD` (`[Category.{vD} D] [Abelian D] [Linear S D]`,
`[HasDerivedCategory.{s'} D]`), a functor `F : C ⥤ D` with `[F.Additive]`,
`[PreservesFiniteLimits F]` and `[PreservesFiniteColimits F]`,
`hF : IsSemilinear R S F`, and a group `Γ : Type uΓ`. Below `K` is an object of
`DerivedCategory C`, `W` an object of `C` with `W₀` the complex `W` placed in
degree `0`, `n : ℤ`, `ρ : Γ →* Aut K` and `σ : Γ →* Aut W`. Write `F K` for
`F.mapDerivedCategory.obj K`, and `ρ_F = (F.mapDerivedCategory.mapAut K).comp ρ`,
`σ_F = (F.mapAut W).comp σ`.

From `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom`
on also `[HasExt.{t} C]` and `[HasExt.{t'} D]`, and the degeneration hypotheses
of `HyperextIsotypicDegenerationBaseChange`: `b : ℤ`,
`hK : ∀ i > b, IsZero (H^i K)`, `hW : ∀ k, ∀ i > 0, Subsingleton (Ext^i(H^k K, W))`
(`Abelian.Ext.{t}`) and `hW' : ∀ k, ∀ i > 0, Subsingleton (Ext^i(H^k (F K), F W))`
(`Abelian.Ext.{t'}`).

| Declaration | Statement |
| --- | --- |
| `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization M F hF ρ σ n hfin h` | Given `hfin : HasFiniteOrbits (abutmentRepresentation R ρ σ n)` and `h : Function.Bijective (abutmentBaseChangeMap F hF K W n)`: `abutmentInvariantsBaseChangeMap F hF ρ σ n` is bijective. |
| `cohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization M F hF ρ σ n hfin h` | Given `hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n)` and `h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))`: `cohomologyHomInvariantsBaseChangeMap F hF ρ σ n` is bijective. |
| `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom M F hF b hK hW hW' n ρ σ hfin h` | Under the degeneration hypotheses, given `hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n)` and `h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))`: `abutmentInvariantsBaseChangeMap F hF ρ σ n` is bijective. |
| `abutmentInvariantsLocalizationEquiv M F hF b hK hW hW' n ρ σ hfin h` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ ≃ₗ[S] (abutmentRepresentation S ρ_F σ_F n)^Γ` with underlying map `abutmentInvariantsBaseChangeMap F hF ρ σ n`. A `def`. |
| `abutmentInvariantsLocalizationEquiv_apply M F hF b hK hW hW' n ρ σ hfin h x` | Its value at `x` is `abutmentInvariantsBaseChangeMap F hF ρ σ n x` (a `simp` lemma, by definition). |

Proofs.

- `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization` and
  `cohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization`: by
  definition, `abutmentInvariantsBaseChangeMap F hF ρ σ n` is
  `invariantsBaseChangeMap` followed by `invariantsLinearMap` of the Library's
  `abutmentBaseChangeIntertwiningMap F hF ρ σ n`, whose underlying map is
  `abutmentBaseChangeMap F hF K W n` (and similarly for
  `cohomologyHomInvariantsBaseChangeMap` with
  `cohomologyHomBaseChangeIntertwiningMap` and
  `cohomologyHomBaseChangeMap F hF K W (-n)`). The first factor is bijective by
  `invariantsBaseChangeMap_bijective_of_isLocalization` and `hfin`, the second
  by `invariantsLinearMap_bijective` and `h`.
- `abutmentInvariantsBaseChangeMap_bijective_of_isLocalization_of_cohomologyHom`:
  the Library's `abutmentInvariantsBaseChangeMap_bijective_iff` reduces the
  claim to the bijectivity of `cohomologyHomInvariantsBaseChangeMap F hF ρ σ n`,
  which is the previous theorem.
- `abutmentInvariantsLocalizationEquiv`: Mathlib's `LinearEquiv.ofBijective`
  applied to the previous theorem.

## Smooth representations

Section `Smooth` takes `R : Type uR` and `S : Type uS` with `[Algebra R S]`,
`[Module.Flat R S]`, `M : Submonoid R` with `[IsLocalization M S]` (`R`, `S`
and `M` explicit), a topological group `G : Type uG` (explicit), instances
`HasDerivedCategory.{s}` on `SmoothRep.{uR, uG, w} R G` and
`HasDerivedCategory.{s'}` on `SmoothRep.{uS, uG, max uS w} S G`, and a group
`Γ : Type uΓ`; the last two declarations also take `HasExt.{t}` and
`HasExt.{t'}` instances on these categories. `K`, `W`, `ρ`, `σ`, `n`, `b`, `hK`,
`hW`, `hW'` are as above with `C` the category `SmoothRep.{uR, uG, w} R G` of
smooth representations of `G` over `R` and `F` the Library's extension of
scalars `E = smoothRepExtendScalars.{w} R S G`. The flatness instance holds for
every localization (Mathlib's `IsLocalization.flat`) and is a separate argument
because the Library's smooth maps take it as an instance.

| Declaration | Statement |
| --- | --- |
| `smoothCohomologyHomInvariantsBaseChangeMap_bijective_of_isLocalization R S M G ρ σ n hfin h` | Given `hfin : HasFiniteOrbits (cohomologyHomRepresentation R ρ σ n)` and `h : Function.Bijective (smoothCohomologyHomBaseChangeMap R S G K W (-n))`: `smoothCohomologyHomInvariantsBaseChangeMap R S G ρ σ n` is bijective. |
| `smoothAbutmentInvariantsBaseChangeMap_bijective_of_isLocalization R S M G b hK hW hW' n ρ σ hfin h` | Under the degeneration hypotheses and the same `hfin`, `h`: `smoothAbutmentInvariantsBaseChangeMap R S G ρ σ n` is bijective. |
| `smoothAbutmentInvariantsLocalizationEquiv R S M G b hK hW hW' n ρ σ hfin h` | `abutmentInvariantsLocalizationEquiv` for `E`: an `S`-linear equivalence from `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ` to the `Γ`-invariants of `abutmentRepresentation S ((E.mapDerivedCategory.mapAut K).comp ρ) ((E.mapAut W).comp σ) n`. A `def`. |

Proofs. The general results for `F = E` and
`hF = smoothRepExtendScalars_isSemilinear R S G`; the smooth maps of the
Library are by definition the general maps for `E`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. `HyperextIsotypicDegenerationBaseChange` reduces the bijectivity of
the base-change map on `Γ`-invariants of the abutment to that of the
corresponding map on `Hom(H^{-n} K, W)`, but leaves the latter open, partly
because extension of scalars need not commute with invariants. This module
isolates one sufficient condition for commutation, a localization `R → S` and
finite orbits, and records its consequences.

The passages of Harris 1999 behind this module are those quoted, from the
rendered scans, in the Markdown files of
`Langlands.Cohomology.HyperextScalarExtension` and
`Langlands.Cohomology.HyperextIsotypicBaseChange`:

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
powers of `ℓ`), so `R = 𝒪`, `S = L_ℓ` is an instance of the hypotheses
`[IsLocalization M S]`; the formalization does not construct this instance.
(5.2) mixes the integral cohomology `H_c(M̆_N, 𝒪(n - 1))` with
`L_ℓ`-coefficients and takes parts cut out by group actions on both sides; this
module shows that taking invariants under a group action with finite orbits
commutes with passing from `𝒪` to `L_ℓ`. Finite orbits occur, for example, for
finite groups (`hasFiniteOrbits_of_finite`) and for smooth representations
restricted to compact subgroups (`hasFiniteOrbits_comp_subtype_of_isSmooth`).
Whether the actions on the hyperext groups in Harris's situation have finite
orbits is not addressed: the module does not identify `Γ`, `K` or `W` with
Harris's objects.

## Scope

- Without finite orbits the conclusion can fail even for a localization. In the
  example of the Markdown file of `Langlands.Cohomology.HyperextIsotypicBaseChange`
  (explanation only, not formalized: `R = ℤ_ℓ`, `S = ℚ_ℓ = ℤ_ℓ[1/ℓ]`,
  `Γ = T = ℚ_ℓ/ℤ_ℓ` acting on `V = ℤ_ℓ ⊕ T` by `γ · (a, t) = (a, t + aγ)`),
  `invariantsBaseChangeMap` is `0 → ℚ_ℓ`; the orbit of `(1, 0)` is
  `{1} × T`, which is infinite.
- The finite-orbit hypotheses `hfin` and the bijectivity hypotheses `h` of the
  base-change maps before taking invariants are not verified for any complex;
  whether they hold in Harris's situation remains an open obligation.
- Only invariants are treated; the base-change maps on isotypic parts for a
  nontrivial `τ` and on multiplicity spaces are not proved bijective here.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.307 and 312 (rendered scans) as quoted in
`Langlands.Cohomology.HyperextScalarExtension` and
`Langlands.Cohomology.HyperextIsotypicBaseChange`.

Dependencies: `Langlands.Cohomology.HyperextIsotypicDegenerationBaseChange`,
`Langlands.Representation.Smooth.Definitions`,
`Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Localization.BaseChange`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
