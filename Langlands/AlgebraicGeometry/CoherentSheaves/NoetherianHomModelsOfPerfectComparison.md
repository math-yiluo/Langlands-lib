# Finite linear models from a universally connective perfect comparison

This module proves the conditional implication

`CoherentSheaves.noetherianHomFiniteLinearModels_of_perfectComparison :
NoetherianHomPerfectComparisonStatement.{u} →
NoetherianHomFiniteLinearModelsStatement.{u}`.

It does **not** prove `NoetherianHomFiniteLinearModelsStatement`. It reduces
that statement to the published intermediate proposition
`NoetherianHomPerfectComparisonStatement`, which is still unproved. The
reduction is the final finite-matrix step in the proof of Stacks Project
Lemma 99.3.8 (Tag 08JX), applied as in the proof of Lemma 99.3.9
(Tag 08JY). The retained source is `08JS.html` in
`stacks-hom-functor-08js-2026-11-02` (folder SHA-256
`2d60cda5ae13d9daa5c318ca4cd199e47a3a00b39f5062492b2207f7b56432c4`).

## Declarations

Let `R : CommRingCat.{u}` and let `K` be an integer cochain complex of
`R`-modules. Assume `ModuleComplex.IsStrictlyPerfect K`: `K` is bounded with
finite projective terms. Assume also that for every `S : CommRingCat.{u}`,
every `φ : R ⟶ S` and every `n < 0`, the homology
`Hⁿ((ModuleComplex.baseChange φ.hom).obj K)` is zero.

- `TensorSections.perfectChart K hK hneg P` is, for a prime `P` of `R`, the
  Library's `ModuleComplex.connectiveFreeChart` of `K` at `P.asIdeal`. Its
  residue-field hypothesis is the vanishing assumption specialized to the
  residue field of `P`. The chart provides `r ∉ P`, a bounded finite free
  complex `C` over `R_r = Localization.Away r` with no negative terms, a
  homotopy equivalence from `C` to `R_r ⊗[R] K`, and coordinate
  isomorphisms of every term of `C` with a finite free module.
- `TensorSections.chartSolutionsIso K hK hneg P` is a natural isomorphism,
  on the entire slice over `Spec R_r`, from the restriction
  `(Over.map j).op ⋙ homologyPresheaf K 0` along
  `j : Spec R_r → Spec R` to
  `FiniteLinearEquations.solutionsPresheaf a`. Here `a` is
  `TensorKernel.matrix` of the actual differential `C⁰ → C¹` in the chart
  coordinates. It is the composite of three isomorphisms:
  1. `homologyPresheafBaseChangeIso`, from the restriction to the tensor
     homology presheaf of `R_r ⊗[R] K` (module `TensorSectionsBaseChange`);
  2. the inverse of `homologyPresheafIsoOfHomotopyEquiv` for the chart's
     homotopy equivalence (module `TensorSectionsHomologyTransport`);
  3. the Library's `homologyZeroSolutionsPresheafIso` for `C`. It applies
     because `C` has zero incoming differential in degree `0`
     (`ConnectiveFreeChart.d_neg_one_zero`).
- `TensorSections.homologyZero_hasLocalModels K hK hneg` proves
  `FiniteLinearEquations.HasLocalModels (homologyPresheaf K 0)`. The cover is
  indexed by `PrimeSpectrum R`, with the chart rings `R_r` and the maps
  `j`. These maps are open immersions by Mathlib's
  `isOpenImmersion_SpecMap_localizationAway`. They are jointly surjective:
  a point `P` lies in the basic open set of its own chart parameter `r ∉ P`,
  which is the open range of `j` by `Scheme.Hom.opensRange_localizationAway`.
  The model on each chart is `chartSolutionsIso`.
- `CoherentSheaves.noetherianHomFiniteLinearModels_of_perfectComparison`
  takes the data `K`, strict perfection, universal vanishing of negative
  homology and the natural isomorphism
  `intrinsicModuleHomPresheaf p M N ≅ homologyPresheaf K 0` supplied by
  `NoetherianHomPerfectComparisonStatement`. It transports
  `homologyZero_hasLocalModels` along the inverse of that isomorphism with
  `HasLocalModels.of_iso`. All hypotheses on `R`, `p`, `M` and `N` are
  passed unchanged to the comparison statement.

The models are local because strict perfection gives finite projective
terms only, and a finite projective module is free only locally. This
matches the open cover in Lemma 99.3.8, where `M` becomes finite free
after replacing the base by the members of an affine open covering.

## Remaining input and why it is not proved here

The only remaining input is `NoetherianHomPerfectComparisonStatement`: a
strictly perfect complex over `R` with universally vanishing negative
homology whose degree-zero tensor homology is the actual Hom presheaf.
Stacks constructs it in the proof of Lemma 99.3.9. That proof first chooses
an approximation `P → M` of the arbitrary coherent source by a perfect
complex (Derived Categories of Spaces, Theorem 75.14.7). It then uses the
perfectness and base-change property of
`Rf_* R𝓗om(P, N)`. The Library has no derived Hom of complexes of module
sheaves, no perfect complexes on schemes and no approximation theorem. The
project operator has ruled (request `61bdc800790e52ebb9afb4f41711657e`,
confirming request `8c746399` of 2026-11-02) that this foundation chain is
not to be started now. The general case stays a tracked goal.

The following routes were examined while working on task
`a304cfdd-31dc-4177-bd36-9565e2239a7a` and do not give a proof for an
arbitrary finitely presented source without new foundations:

- **Global locally free presentation.** EGA III 7.7.8 represents
  `Hom(𝒢, ℱ ⊗ -)` only when the source `𝒢` is a cokernel of a map of finite
  locally free sheaves. Remark 7.7.9(iii) defers the general case to the
  never-written Chapter V. Sources: `grothendieck-ega-iii-2-1963`,
  Section 7.7 (7.7.8, 7.7.9). A proper scheme need not have the resolution
  property, so this hypothesis cannot be produced in general.
- **Čech and local-presentation complexes with Mumford's lemma.** Gluing
  local presentations of `M` over a finite affine cover gives a two-term
  complex of flat modules whose `H⁰` after base change is the Hom functor.
  Its top cohomology is not finitely generated, so the Library's Mumford
  lemma (`Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`)
  does not apply. A bounded flat complex whose cohomology is finitely
  generated only in low degrees is not enough: the extended Čech complex
  computing local cohomology on `k[x,y]` has `H⁰ = H¹ = 0`, yet its `H⁰`
  functor is the non-representable `Γ_𝔪`. Infinite twisted resolutions
  avoid gluing obstructions but are unbounded above. The abstract claim
  that a complex `C` of flat modules in degrees `≥ 0` whose cohomology
  modules are all finitely generated has representable `I ↦ H⁰(C ⊗ I)` is
  false in general (counterexample 1 below). Bounding twisted resolutions
  requires the perfect approximation itself.
- **Dévissage.** Dévissage on the source fails because Ext out of
  pushforwards along Chow modifications or closed immersions is not
  compatible with base change. Dévissage on the target fails because strict
  transforms of an `R`-flat sheaf under a Chow modification need not be
  `R`-flat.
- **Formal functions and completion.** Over complete local rings the
  Library's formal Hom theorem
  (`OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`)
  and an Artinian argument give representability. Passing back to an open
  neighbourhood needs a semicontinuity input: a functor can be
  representable over every local ring of the base but over no
  neighbourhood of the generic point (counterexample 2 below).
- **Duality.** Hall's coherence theorem for `Extⁱ(M, N ⊗ -)` (source
  `hall-cohomology-base-change-stacks-arxiv-1206-4179v2`, Theorems B and C)
  uses Grothendieck duality with dualizing complexes. That is also absent
  from the Library.

Both counterexamples use one fact. A representable functor `Hom(Q, -)`
preserves products, so a functor `T` whose canonical map
`T(∏ₗ Iₗ) → ∏ₗ T(Iₗ)` is not surjective is not representable. Neither
counterexample is used by the Lean code.

**Counterexample 1.** Let `A = S⁻¹k[x₁, x₂, …]` be Nagata's noetherian ring
of infinite Krull dimension. Source: `stacks-nagata-koszul-depth-2026-11-10`
(folder SHA-256
`ca375da7941622d298748428e3f84fa55fcd26c5d12bf1d563a3d8133a9395bd`), file
`02JC.html`, Section 110.16 (Tag 02JC). Its maximal ideals are
`𝔪ᵢ = 𝔭ᵢA`, where `𝔭ᵢ` is generated by the `dᵢ = 2^(i-1)` variables
`x_{2^(i-1)}, …, x_{2^i - 1}`. The page states the local dimension as
`2^i`; its comment #11699 corrects this off-by-one. Put
`Bᵢ = A_{𝔪ᵢ} = k[x₁, x₂, …]_{𝔭ᵢ}`. The `dᵢ` variables form a regular sequence
in the maximal ideal of `Bᵢ`, which they generate. Let `Kᵢ` be their
homological Koszul complex over `Bᵢ`. By Lemma 15.31.2 (Tag 062F, file
`062F.html`), `Kᵢ` is a finite free resolution of
`Bᵢ/𝔪ᵢBᵢ = κ(𝔪ᵢ)`. Let `Cᵢ = Hom_{Bᵢ}(Kᵢ, Bᵢ)`, in degrees `0, …, dᵢ`,
and `C = ⊕ᵢ Cᵢ`.

- Every term of `C` is flat over `A`: it is a sum of finite free modules
  over the flat `A`-algebras `Bᵢ`.
- `Hʲ(Cᵢ) = Extʲ_{Bᵢ}(κ(𝔪ᵢ), Bᵢ)`. This vanishes for `j > dᵢ` by degrees.
  It also vanishes for `j < dᵢ`. Indeed `depth Bᵢ ≥ dᵢ` by Definition
  10.72.1 (Tag 00LI, file `00LI.html`), and Lemma 10.72.5 (Tag 00LW, file
  `00LW.html`) identifies depth with the least `j` with nonzero
  `Extʲ(κ, -)`. For `j = dᵢ` it is a finite `Bᵢ`-module killed by `𝔪ᵢ`.
  So it is a finite-dimensional `κ(𝔪ᵢ)`-vector space, which is finitely
  generated over `A`.
- The `dᵢ = 1, 2, 4, …` are pairwise distinct. So `Hʲ(C) = ⊕ᵢ Hʲ(Cᵢ)` is
  either `0` or `H^{dᵢ}(Cᵢ)` for the single `i` with `dᵢ = j`, and it is
  finitely generated. In particular `H⁰(C) = 0`. Infinite Krull
  dimension is used exactly here. Over a ring of finite dimension, the `dᵢ`
  would be bounded and some degree would collect infinitely many residue
  fields.
- For an `A`-module `I`, `Cᵢ ⊗_A I = Hom_{Bᵢ}(Kᵢ, I_{𝔪ᵢ})` because `Kᵢ` is
  finite free. Its `H⁰` is `Hom_{Bᵢ}(κ(𝔪ᵢ), I_{𝔪ᵢ}) = Hom_A(κ(𝔪ᵢ), I)`.
  For the last equality: `A/𝔪ᵢ` is finitely presented, so
  `Hom_A(κ(𝔪ᵢ), I)` localizes at `𝔪ᵢ` to `Hom_{Bᵢ}(κ(𝔪ᵢ), I_{𝔪ᵢ})`. It is
  also a `κ(𝔪ᵢ)`-vector space, so localization at `𝔪ᵢ` does not change it.
  Sums commute with `⊗` and with cohomology, so
  `H⁰(C ⊗ I) = ⊕ᵢ Hom_A(κ(𝔪ᵢ), I)`.
- Take `I = ∏ₗ κ(𝔪ₗ)`. Then `Hom_A(κ(𝔪ᵢ), κ(𝔪ₗ)) = 0` for `i ≠ l`, so the
  canonical map is the inclusion `⊕ᵢ κ(𝔪ᵢ) → ∏ᵢ κ(𝔪ᵢ)`. It is not
  surjective, so `I ↦ H⁰(C ⊗ I)` is not representable.

**Counterexample 2.** Let `k` be a field of characteristic zero, so the
integers `n ∈ ℕ` are pairwise distinct in `k`. On `k[x]`-modules put
`T(I) = ⊕_{n ∈ ℕ} I[x - n]`, where `I[x - n] = {a ∈ I | (x - n)a = 0}`.

- **At every prime `𝔭`.** On `k[x]_𝔭`-modules, `x - n` acts invertibly
  unless `𝔭 = (x - n)`, so at most one summand survives. Thus `T` is
  `Hom(κ(𝔭), -)` if `𝔭 = (x - n)` for some `n ∈ ℕ`, and `0` otherwise.
  Both are representable.
- **On every neighbourhood of the generic point.** Let `f ≠ 0`. The set
  `S_f = {n ∈ ℕ | f(n) ≠ 0}` is infinite, because `f` has finitely many
  roots. On `k[x]_f`-modules, `T(I) = ⊕_{n ∈ S_f} I[x - n]`. For `n ∉ S_f`,
  `x - n` divides `f` and acts invertibly. Take
  `I = ∏_{m ∈ S_f} κ(m)` with `κ(m) = k[x]/(x - m)`, which are
  `k[x]_f`-modules. The canonical map is the inclusion
  `⊕_{n ∈ S_f} κ(n) → ∏_{n ∈ S_f} κ(n)`. It is not surjective, so `T` is
  not representable over `k[x]_f`.

The characteristic-zero hypothesis is necessary. Over `k = 𝔽_p`, all
`n ≡ 0 mod p` give the same summand `I[x]`. Then `T` is not representable
at the prime `(x)`, and `T = 0` on `D(x^p - x)`.

Provenance: the matrix step follows the cited Stacks proof. The base-change
and homotopy transports are internal constructions from Mathlib and the
Library's `ConnectiveFreeChart`, `TensorHomologyMatrix` and
`ExtendScalarsTensor`.
