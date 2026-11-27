# Continued cuspidal-test expansions: reduction to standard parabolics

Module `Langlands.Global.AdelicEisensteinCuspidalTestStandardizationReduction` defines three
propositions and proves two implications:

- `Langlands.Global.EisensteinCuspidalTestStandardizationStatement`: the passage of the cuspidal
  tests of Eisenstein series from a presented parabolic `P` to a standard parabolic `P_I`;
- `Langlands.Global.EisensteinCuspidalTestContinuedExpansionStandardizationReductionStatement`:
  the implication
  `EisensteinCuspidalTestStandardizationStatement → EisensteinCuspidalTestStandardExpansionStatement
  → EisensteinCuspidalTestContinuedExpansionStatement`, proved by
  `Langlands.Global.eisensteinCuspidalTestContinuedExpansionStandardizationReduction`;
- `Langlands.Global.EisensteinCuspidalTestContinuedExpansionReductionStatement`: the implication
  `EisensteinCuspidalTestStandardizationStatement → EisensteinCuspidalTestIntertwiningExpansionStatement
  → IntertwiningRestrictedCuspidalTestContinuationStatement →
  EisensteinCuspidalTestContinuedExpansionStatement`, proved by
  `Langlands.Global.eisensteinCuspidalTestContinuedExpansionReduction`.

All propositions are in universe `u`. The target `EisensteinCuspidalTestContinuedExpansionStatement`
is defined in `Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneReduction`, which proves
that it implies `EisensteinCuspidalTestRootHyperplaneStatement`. The standard expansion
`EisensteinCuspidalTestStandardExpansionStatement`, the tested constant-term formula
`EisensteinCuspidalTestIntertwiningExpansionStatement` and the restricted continuation
`IntertwiningRestrictedCuspidalTestContinuationStatement` are defined in
`Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction`, whose Markdown describes
them and the common setting of standard families. This module proves none of the premises.

## `EisensteinCuspidalTestStandardizationStatement`

The binders and hypotheses are those of `EisensteinCuspidalTestContinuedExpansionStatement`, in
the same order, up to the automorphy of `φ`, with the Iwasawa coverage of the minimal standard
parabolic named `h₀`. So `G` is connected reductive over a number field `F`; `p : P → G` is a
parabolic with geometric unipotent radical `iU`, rational Levi `l` and split component
`a : A → M`, presented by `r : ParabolicRootPresentation p l a`, with `hA`, `hT` the split torus
hypotheses; `𝓕` is a standard parabolic family; `K` is a maximal compact subgroup with
`P(𝔸) K = G(𝔸)` (`hK`), `P₀(𝔸) K = G(𝔸)` (`h₀`) and `K ∩ M_J(𝔸)` maximal compact in `M_J(𝔸)` for
every standard `J`; `rho` is a closed matrix embedding; and `φ` is automorphic on
`U(𝔸) M(F) \ G(𝔸)` for `Kinf = K.comap (ofInfinite F G)`. The parabolic `P` need not be standard
for `𝓕`.

The assertion: there are a standard index `I`, a complex linear isomorphism
`iota : X^*(P) ⊗ ℂ ≃ X^*(P_I) ⊗ ℂ`, `m : ℕ`, functions `E j` on `X^*(P) ⊗ ℂ` and functions `φ' j`
on `G(𝔸)` (`j : Fin m`) such that

1. every `φ' j` is automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)` (`𝓕.IsAutomorphicOn hsmooth Kinf rho I`);
2. every `E j` is entire in linear coordinates: `E j ∘ e` is complex differentiable on `ℂⁿ` for
   every complex linear isomorphism `e : ℂⁿ ≃ X^*(P) ⊗ ℂ`;
3. with some instances `Fintype (relativeWeylGroup 𝓕.i)` and
   `∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left` (quantified existentially; the first
   is a subsingleton and the second a proposition), which are required by the root forms and the
   regularity predicate of the standard presentation `𝓕.rootPresentation I` of `P_I` (module
   `Langlands.Global.AdelicIntertwiningElementaryChainStatement`; the presentation itself is formed
   from the family and the index alone):
   - *regularity transport*: for every `R` there is `R'` such that `iota λ` is `R`-regular for
     `𝓕.rootPresentation I` whenever `λ` is `R'`-regular for `r`;
   - *root forms*: for every root `β'` of `A_I` in `U_I` there are a root `β` of `A` in `U` and
     `s ≠ 0` with
     `(𝓕.rootPresentation I).rootFunctional hA_I hT_I β' ∘ₗ iota = s • r.rootFunctional hA hT β`,
     where `hA_I = (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1` and
     `hT_I = 𝓕.maximalSplit.isSplitSubtorus.1`;
   - *tested comparison*: there is `R` such that for every `R`-regular `λ` for `r`, every
     standard `J`, every cusp form `ψ` on `M_J(F) \ M_J(𝔸)` and every `g`,
     `𝓕.leviPairing J (𝓕.constantTerm J (hK.eisensteinSeries φ λ)) g ψ =
     ∑ j, E j λ * 𝓕.leviPairing J (𝓕.constantTerm J (E_{P_I}(φ' j, iota λ))) g ψ`,
     where `E_{P_I}` is `(𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries`.

### Source and derivation

Provenance: derived. Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024) (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`),
work with standard parabolics of a fixed minimal parabolic and a maximal compact subgroup in good
position (§2.1, pp. 189–190, TeX lines 345–413; the series (2.1) in §2.2, p. 191, TeX lines
415–431). Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995)
(`moeglin-waldspurger-1995-spectral-decomposition`), I.1.4, pp. 4–5, describe maximal compact
subgroups in good position; their II.1.5, pp. 85–87, treats the convergence of Eisenstein series
for the standard parabolic fixed in II.1.1 (p. 78) and the automorphic inducing data stated
there. Neither source treats an arbitrary presented parabolic: the statement records the passage
from such a parabolic to a standard one for a fixed compact `K` in good position, and the
rational-conjugation calculation below gives this comparison.

Why it holds. There is `γ ∈ G(F)` with `γ P γ⁻¹ = P_I` for a standard `P_I` and, after
multiplying `γ` on the left by an element of `P_I(F)`, `γ M γ⁻¹ = M_I` and `γ A γ⁻¹ = A_I`. The
heights `H_P` and `H_{P_I}` for `K` are right `K`-invariant, satisfy `H_P(x y) = H_P(x) + H_P(y)`
for `x ∈ P(𝔸)` (and likewise for `P_I`), and `H_{P_I}(γ x γ⁻¹) = γ · H_P(x)` for `x ∈ P(𝔸)`.
First, `H_P(γ⁻¹ k) = H_P(γ⁻¹)` for every `k ∈ K`: write `γ⁻¹ k = x κ` with `x ∈ P(𝔸)` and
`κ ∈ K`; then `γ κ = (γ x γ⁻¹)⁻¹ k`, so
`H_{P_I}(γ) = H_{P_I}(γ κ) = -H_{P_I}(γ x γ⁻¹) = -γ · H_P(x)`, and
`H_P(γ⁻¹ k) = H_P(x) = -γ⁻¹ · H_{P_I}(γ)` does not depend on `k`. Writing `y = u m k` with
`u ∈ U_I(𝔸)`, `m ∈ M_I(𝔸)`, `k ∈ K`, so that `γ⁻¹ y = (γ⁻¹ u m γ) γ⁻¹ k` with
`γ⁻¹ u m γ ∈ P(𝔸)`, gives `H_P(γ⁻¹ y) = γ⁻¹ · H_{P_I}(y) + H_P(γ⁻¹)`, so
`φ_λ(γ⁻¹ y) = e^{⟨λ, H_P(γ⁻¹)⟩} (φ(γ⁻¹ ·))_{γλ}(y)`. Since `δ ↦ γδ` is a bijection
`P(F) \ G(F) → P_I(F) \ G(F)`, this gives
`E_P(φ, λ) = e^{⟨λ, H_P(γ⁻¹)⟩} E_{P_I}(φ(γ⁻¹ ·), γλ)` in the range of convergence. This is the
assertion with `m = 1`, `φ' 0 = φ(γ⁻¹ ·)`, which is automorphic along `P_I`, `E 0` the exponential
of a linear form, and `iota` the transport `λ ↦ γλ` of characters by conjugation (the statement
allows finitely many terms with entire coefficients; one term suffices). The constant
terms and the Levi pairings are linear for scalar multiples, so the tested comparison follows
without any integrability condition. Conjugation by `γ` (followed by an element of `M_I(F)`
moving the maximal split torus of `r` to that of `𝓕`) carries the roots of `A` in `U` to the roots
of `A_I` in `U_I`. The positive forms used by the two presentations are averages over the
relative Weyl groups of positive forms; they agree up to a positive factor on each irreducible
component of the relative root system, and both induce the orthogonal projection onto the
characters of the split component, which does not depend on these factors. Hence the pull-back
of the root form of `β'` is a positive multiple of the root form of the corresponding `β`, and
regularity is transported with a rescaled bound.

## The reductions

### `eisensteinCuspidalTestContinuedExpansionStandardizationReduction`

It takes the standardization, the standard expansion and the data of
`EisensteinCuspidalTestContinuedExpansionStatement`, including the standard index `J`.

1. The standardization gives `I`, `iota`, `m`, `E`, `φ'`, the two instances, the regularity
   transport, the root-form comparison and a bound `R₀`. The instances are then local instances,
   so that the standard expansion can be applied to `𝓕`.
2. The standard expansion, applied for each `j : Fin m` to `I`, `φ' j` and `J`, gives `k j`,
   `Φ j`, `L j`, `c j`, `D j` and a bound `R j`. The regularity transport gives, for each `j`, a
   bound `R' j` such that `R' j`-regularity for `r` implies `R j`-regularity of `iota λ`
   (`choose`). The root-form comparison gives functions `σ` (a root of `A` for every root of
   `A_I`) and `s` (the factors), by `choose!`.
3. The terms are indexed by `κ = Σ j, Fin (k j)`, enumerated by `Fintype.equivFin`. For the index
   corresponding to `(j, i)` the expansion uses `Φ j i`, the linear map `L j i ∘ₗ iota` and the
   coefficient `λ ↦ E j λ * c j i (iota λ)`. The domain is `Dc = ⋂_{(j, i) ∈ κ} iota ⁻¹' D j`, open
   and dense in coordinates since each `D j` with `k j > 0` is
   (`isOpenDenseInCoordinates_iInter_of_finite`; a coordinate system of `X^*(P) ⊗ ℂ` composed with
   `iota` is one of `X^*(P_I) ⊗ ℂ`).
4. Meromorphy: `c j i ∘ iota` is meromorphic in coordinates with domain `iota ⁻¹' D j`
   (`IsMeromorphicInCoordinatesOn.comp_linearEquiv`), `E j` is meromorphic with domain the whole
   space (`isMeromorphicInCoordinatesOn_univ`), their product is meromorphic on the intersection
   (`IsMeromorphicInCoordinatesOn.mul`), and `IsMeromorphicInCoordinatesOn.congr_mono` restricts
   the domain to `Dc`.
5. Poles: `HasRootHyperplanePoles.comp_linearEquiv_of_proportional` (module
   `Langlands.Analysis.Meromorphic.RootHyperplanePoles`) turns the poles of `c j i` along the root
   forms of `P_I` into poles of `c j i ∘ iota` along the root forms of `P`, using `σ`, `s` and the
   comparison of forms; `E j` has no poles (`hasRootHyperplanePoles_of_differentiable`);
   `HasRootHyperplanePoles.mul` and `HasRootHyperplanePoles.mono` give the poles of the product on
   `Dc`.
6. Agreement: the bound is `max R₀ 0 + ∑ j, |R' j|` (`le_max_zero_add_sum_abs`). For a regular
   `λ`, the tested comparison writes the test of `C_J E_P(φ, λ)` as `∑ j, E j λ` times the tests of
   `C_J E_{P_I}(φ' j, iota λ)`; each of these is expanded by the standard expansion at the regular
   parameter `iota λ`; `Finset.mul_sum`, `Fintype.sum_sigma` and `Equiv.sum_comp` rewrite the
   result as the sum over `Fin (Fintype.card κ)`. The twist on the right is formed with the
   Iwasawa coverage `𝓕.isIwasawaCompact_of_minimal h₀ J`; any other proof of the same coverage
   gives the same twist.

### `eisensteinCuspidalTestContinuedExpansionReduction`

It composes the previous reduction with
`eisensteinCuspidalTestStandardExpansionReduction` (module
`Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction`), which derives the standard
expansion from the tested constant-term formula and the restricted continuation.

## Scope

Only the number field case is stated. The module proves the two implications and does not prove
`EisensteinCuspidalTestStandardizationStatement`.
