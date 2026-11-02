# Invariants of hyperext abutments and localization for finitely generated cohomology

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextInvariantsLocalization`
(`invariantsLinearMap_bijective`; Worker 61) and
`Langlands.Cohomology.HyperextHomLocalization`
(`invariantsBaseChangeMap_bijective_of_isSMulRegular`,
`repCohomologyHomBaseChangeMap_bijective_of_isLocalization`,
`smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization`,
`repHom_isSMulRegular`, `smoothRepHom_isSMulRegular`; Worker 61). Through
these imports it also uses
`Langlands.Cohomology.HyperextIsotypicDegenerationBaseChange`
(`invariantsLinearMap`, `abutmentInvariantsBaseChangeMap`,
`cohomologyHomInvariantsBaseChangeMap`,
`abutmentInvariantsBaseChangeMap_bijective_iff`,
`smoothAbutmentInvariantsBaseChangeMap`,
`smoothCohomologyHomInvariantsBaseChangeMap`; Worker 61),
`Langlands.Cohomology.HyperextIsotypicBaseChange`
(`invariantsBaseChangeMap`, `cohomologyHomBaseChangeIntertwiningMap`; Worker
61), `Langlands.Cohomology.HyperextScalarExtension` (`IsSemilinear`,
`cohomologyHomBaseChangeMap`, `smoothCohomologyHomBaseChangeMap`,
`repExtendScalars_isSemilinear`, `smoothRepExtendScalars_isSemilinear`; Worker
61), `Langlands.Cohomology.HyperextDegenerationIsotypic`
(`abutmentRepresentation`, `cohomologyHomRepresentation`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (`repExtendScalars`;
Worker 61) and `Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension`
(`smoothRepExtendScalars`; Worker 61).

Let `S` be the localization of a commutative ring `R` at a submonoid `M`. The
Library's `HyperextInvariantsLocalization` proves the base-change maps on
`Γ`-invariants of hyperext groups bijective under a finite-orbit hypothesis on
the action of `Γ`, and `HyperextHomLocalization` proves the base-change map on
`Hom(H^q K, W)` bijective for extension of scalars of (smooth) representations
when `H^q K` is finitely generated and `W` has no `M`-torsion. This module
combines them. When `Hom(H^{-n} K, W)` has no `M`-torsion, invariants commute
with localization without any finite-orbit hypothesis, so for extension of
scalars of (smooth) representations the base-change maps on `Γ`-invariants of
`Hom(H^{-n} K, W)` and, under the degeneration hypotheses, of `Hom(K, W₀⟦n⟧)`
are bijective as soon as `H^{-n} K` is finitely generated over `R[G]` and `W`
has no `M`-torsion. These hypotheses, and the degeneration hypotheses, remain
explicit.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`
and use the Library's `HyperextAbutment` namespace (`open HyperextAbutment`).
For a representation `ρ` of `Γ`, `ρ^Γ` denotes Mathlib's `ρ.invariants`. "`V`
has no `M`-torsion" means `∀ m : M, IsSMulRegular V (m : R)`.

## Exact semilinear functors

Section `Derived` takes commutative rings `R : Type uR`, `S : Type uS` with
`[Algebra R S]` (implicit), a submonoid `M : Submonoid R` with
`[IsLocalization M S]` (explicit), an `R`-linear abelian category
`C : Type uC` (`[Category.{vC} C] [Abelian C] [Linear R C]`,
`[HasDerivedCategory.{s} C]`), an `S`-linear abelian category `D : Type uD`
(`[Category.{vD} D] [Abelian D] [Linear S D]`, `[HasDerivedCategory.{s'} D]`),
a functor `F : C ⥤ D` with `[F.Additive]`, `[PreservesFiniteLimits F]` and
`[PreservesFiniteColimits F]`, `hF : IsSemilinear R S F`, and a group
`Γ : Type uΓ`. Below `K` is an object of `DerivedCategory C`, `W` an object of
`C` with `W₀` the complex `W` placed in degree `0`, `n : ℤ`,
`H^i K = (homologyFunctor C i).obj K`, `ρ : Γ →* Aut K` and `σ : Γ →* Aut W`.
Write `F K` for `F.mapDerivedCategory.obj K`, and
`ρ_F = (F.mapDerivedCategory.mapAut K).comp ρ`, `σ_F = (F.mapAut W).comp σ`.
The two hypotheses on `Hom(H^{-n} K, W)` are
`hreg : ∀ m : M, IsSMulRegular (H^{-n} K ⟶ W) (m : R)` and
`h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))`.

From `abutmentInvariantsBaseChangeMap_bijective_of_isSMulRegular` on the
section also takes `[HasExt.{t} C]` and `[HasExt.{t'} D]`, and the degeneration
hypotheses of `HyperextIsotypicDegenerationBaseChange`: `b : ℤ`,
`hK : ∀ i > b, IsZero (H^i K)`,
`hW : ∀ k, ∀ i > 0, Subsingleton (Ext^i(H^k K, W))` (`Abelian.Ext.{t}`) and
`hW' : ∀ k, ∀ i > 0, Subsingleton (Ext^i(H^k (F K), F W))` (`Abelian.Ext.{t'}`).

| Declaration | Statement |
| --- | --- |
| `cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular M F hF ρ σ n hreg h` | `cohomologyHomInvariantsBaseChangeMap F hF ρ σ n : S ⊗[R] (cohomologyHomRepresentation R ρ σ n)^Γ → (cohomologyHomRepresentation S ρ_F σ_F n)^Γ` is bijective. |
| `abutmentInvariantsBaseChangeMap_bijective_of_isSMulRegular M F hF b hK hW hW' n ρ σ hreg h` | Under the degeneration hypotheses, `abutmentInvariantsBaseChangeMap F hF ρ σ n : S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ → (abutmentRepresentation S ρ_F σ_F n)^Γ` is bijective. |
| `abutmentInvariantsLocalizationEquivOfIsSMulRegular M F hF b hK hW hW' n ρ σ hreg h` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ ≃ₗ[S] (abutmentRepresentation S ρ_F σ_F n)^Γ` with underlying map `abutmentInvariantsBaseChangeMap F hF ρ σ n`. A `def`. |
| `abutmentInvariantsLocalizationEquivOfIsSMulRegular_apply M F hF b hK hW hW' n ρ σ hreg h x` | Its value at `x` is `abutmentInvariantsBaseChangeMap F hF ρ σ n x` (a `simp` lemma, by definition). |

Proofs.

- `cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular`: by
  definition, `cohomologyHomInvariantsBaseChangeMap F hF ρ σ n` is
  `invariantsBaseChangeMap S (cohomologyHomRepresentation R ρ σ n)` followed by
  `invariantsLinearMap` of the Library's
  `cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n`, whose underlying map is
  `cohomologyHomBaseChangeMap F hF K W (-n)`. The representation
  `cohomologyHomRepresentation R ρ σ n` acts on `H^{-n} K ⟶ W`, so the first
  factor is bijective by `invariantsBaseChangeMap_bijective_of_isSMulRegular`
  and `hreg`; the second is bijective by `invariantsLinearMap_bijective` and
  `h`.
- `abutmentInvariantsBaseChangeMap_bijective_of_isSMulRegular`: the Library's
  `abutmentInvariantsBaseChangeMap_bijective_iff` reduces the claim to the
  previous theorem.
- `abutmentInvariantsLocalizationEquivOfIsSMulRegular`: Mathlib's
  `LinearEquiv.ofBijective` applied to the previous theorem.

## Representations

Section `Rep` takes `R : Type uR` and `S : Type uS` with `[Algebra R S]`,
`[Module.Flat R S]`, `M : Submonoid R` with `[IsLocalization M S]`, a monoid
`G : Type uG` (`R`, `S`, `M` and `G` explicit), instances
`HasDerivedCategory.{s}` on `Rep.{w} R G` and `HasDerivedCategory.{s'}` on
`Rep.{max uS w} S G`, and a group `Γ : Type uΓ`; the last two declarations also
take `HasExt.{t}` and `HasExt.{t'}` instances on these categories. `K`, `W`,
`ρ`, `σ`, `n`, `b`, `hK`, `hW`, `hW'` are as above with `C` the category
`Rep.{w} R G` and `F` the Library's extension of scalars
`E = repExtendScalars.{w} R S G`, `hF = repExtendScalars_isSemilinear.{w} R S G`.
The flatness instance holds for every localization (Mathlib's
`IsLocalization.flat`) and is a separate argument because the Library derives
the exactness instances of `E` from it. Every declaration takes
`[Module.Finite (MonoidAlgebra R G) (H^{-n} K).ρ.asModule]` (finite generation
of `H^{-n} K` over `R[G]`) and `hreg : ∀ m : M, IsSMulRegular W (m : R)`.

| Declaration | Statement |
| --- | --- |
| `repCohomologyHomInvariantsBaseChangeMap_bijective_of_finite R S M G ρ σ n hreg` | `cohomologyHomInvariantsBaseChangeMap E hF ρ σ n` is bijective. |
| `repAbutmentInvariantsBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ hreg` | Under the degeneration hypotheses, `abutmentInvariantsBaseChangeMap E hF ρ σ n` is bijective. |
| `repAbutmentInvariantsLocalizationEquiv R S M G b hK hW hW' n ρ σ hreg` | Under the same hypotheses, the `S`-linear equivalence from `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ` to the `Γ`-invariants of `abutmentRepresentation S ((E.mapDerivedCategory.mapAut K).comp ρ) ((E.mapAut W).comp σ) n` with underlying map `abutmentInvariantsBaseChangeMap E hF ρ σ n`. A `def`. |

Proofs.

- `repCohomologyHomInvariantsBaseChangeMap_bijective_of_finite`:
  `cohomologyHomInvariantsBaseChangeMap_bijective_of_isSMulRegular` with
  `hreg` for `H^{-n} K ⟶ W` from the Library's `repHom_isSMulRegular` and `h`
  from the Library's `repCohomologyHomBaseChangeMap_bijective_of_isLocalization`
  (for `q = -n`).
- `repAbutmentInvariantsBaseChangeMap_bijective_of_finite`: the Library's
  `abutmentInvariantsBaseChangeMap_bijective_iff` and the previous theorem.
- `repAbutmentInvariantsLocalizationEquiv`: Mathlib's
  `LinearEquiv.ofBijective` applied to the previous theorem.

## Smooth representations

Section `Smooth` takes `R`, `S`, `M` as in section `Rep`, a topological group
`G : Type uG` (`[Group G] [TopologicalSpace G]`, explicit), instances
`HasDerivedCategory.{s}` on `SmoothRep.{uR, uG, w} R G` and
`HasDerivedCategory.{s'}` on `SmoothRep.{uS, uG, max uS w} S G`, and a group
`Γ : Type uΓ`; the last two declarations also take `HasExt.{t}` and
`HasExt.{t'}` instances on these categories. `K`, `W`, `ρ`, `σ`, `n`, `b`,
`hK`, `hW`, `hW'` are as above with `C` the category
`SmoothRep.{uR, uG, w} R G` of smooth representations and `F` the Library's
`E' = smoothRepExtendScalars.{w} R S G`. Every declaration takes
`[Module.Finite (MonoidAlgebra R G) (H^{-n} K).obj.ρ.asModule]` (finite
generation over `R[G]` of the underlying representation of `H^{-n} K`) and
`hreg : ∀ m : M, IsSMulRegular W (m : R)`.

| Declaration | Statement |
| --- | --- |
| `smoothCohomologyHomInvariantsBaseChangeMap_bijective_of_finite R S M G ρ σ n hreg` | The Library's `smoothCohomologyHomInvariantsBaseChangeMap R S G ρ σ n` is bijective. |
| `smoothAbutmentInvariantsBaseChangeMap_bijective_of_finite R S M G b hK hW hW' n ρ σ hreg` | Under the degeneration hypotheses, the Library's `smoothAbutmentInvariantsBaseChangeMap R S G ρ σ n` is bijective. |
| `smoothAbutmentInvariantsLocalizationEquivOfFinite R S M G b hK hW hW' n ρ σ hreg` | Under the same hypotheses, the `S`-linear equivalence from `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ` to the `Γ`-invariants of `abutmentRepresentation S ((E'.mapDerivedCategory.mapAut K).comp ρ) ((E'.mapAut W).comp σ) n` with underlying map `smoothAbutmentInvariantsBaseChangeMap R S G ρ σ n`. A `def`. |

Proofs. As for representations, with the Library's
`smoothRepHom_isSMulRegular` and
`smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization`; the smooth maps
of the Library are by definition the general maps for `E'` and
`smoothRepExtendScalars_isSemilinear R S G`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from the Library.
`HyperextIsotypicDegenerationBaseChange` reduces the bijectivity of the
base-change map on `Γ`-invariants of the abutment to that of the corresponding
map on `Hom(H^{-n} K, W)`; `HyperextInvariantsLocalization` proves the latter
under finite orbits. This module replaces the finite-orbit hypothesis by
finiteness and torsion-freeness hypotheses on `H^{-n} K` and `W`.

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
instance. (5.2) combines a degeneration with parts cut out by group actions, and
mixes integral cohomology with `L_ℓ`-coefficients. This module shows that,
for the degeneration of `HyperextIsotypicDegenerationBaseChange`, the parts
fixed by a group `Γ` acting on `K` and `W` are compatible with passing from `𝒪`
to `L_ℓ` when `H^{-n} K` is finitely generated over `𝒪[G]` and `W` has no
`ℓ`-torsion. The module does not identify `G`, `Γ`, `K` or `W` with Harris's
objects. Whether Harris's cohomology groups are finitely generated over the
relevant group algebra, and whether the degeneration hypotheses hold in his
situation, are not addressed.

## Scope

- The finite generation of `H^{-n} K` over `R[G]`, the absence of `M`-torsion
  in `W` (or, in section `Derived`, in `Hom(H^{-n} K, W)`), the bijectivity
  hypothesis `h` of section `Derived` and the degeneration hypotheses are not
  verified for any complex; whether they hold in Harris's situation remains an
  open obligation.
- Only invariants are treated; the base-change maps on isotypic parts for a
  nontrivial `τ` and on multiplicity spaces are not proved bijective here.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.307 and 312 (rendered scans) as quoted in
`Langlands.Cohomology.HyperextScalarExtension`,
`Langlands.Cohomology.HyperextInvariantsLocalization` and
`Langlands.Cohomology.HyperextHomLocalization`.

Dependencies: `Langlands.Cohomology.HyperextInvariantsLocalization` and
`Langlands.Cohomology.HyperextHomLocalization`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
