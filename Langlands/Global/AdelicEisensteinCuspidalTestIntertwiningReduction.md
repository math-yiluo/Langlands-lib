# Continued cuspidal-test expansions for standard parabolics from the tested (6.18)

Module `Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction` defines four
propositions and proves one implication between them:

- `Langlands.Global.EisensteinCuspidalTestStandardExpansionStatement`: the continued
  cuspidal-test expansion for a standard parabolic `P_I`;
- `Langlands.Global.EisensteinCuspidalTestIntertwiningExpansionStatement`: the constant-term
  formula (6.18) of Bernstein–Lapid, tested against cusp forms, in the range of convergence;
- `Langlands.Global.IntertwiningRestrictedCuspidalTestContinuationStatement`: the meromorphic
  continuation, in parameters `λ ∈ X^*(P_I) ⊗ ℂ`, of the cuspidal tests of the intertwining terms
  of (6.18), with poles along the root hyperplanes of `P_I`;
- `Langlands.Global.EisensteinCuspidalTestStandardExpansionReductionStatement`: the implication
  `EisensteinCuspidalTestIntertwiningExpansionStatement →
  IntertwiningRestrictedCuspidalTestContinuationStatement →
  EisensteinCuspidalTestStandardExpansionStatement` (all in universe `u`), proved by
  `Langlands.Global.eisensteinCuspidalTestStandardExpansionReduction`.

It also proves the elementary inequality `Langlands.Global.le_max_zero_add_sum_abs`: for a real
number `R₀` and a family `R : Fin k → ℝ`, both `R₀` and every `R t` are at most
`max R₀ 0 + ∑ t, |R t|`.

The module does not prove any of the three premises. The module
`Langlands.Global.AdelicEisensteinCuspidalTestStandardizationReduction` combines the standard
expansion with a passage to standard parabolics to obtain
`EisensteinCuspidalTestContinuedExpansionStatement` (module
`Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneReduction`).

## The common setting

The three propositions of this module that quantify over a standard family — the standard
expansion, the tested constant-term formula and the restricted continuation — share the
following binders and hypotheses. The passage to standard parabolics,
`EisensteinCuspidalTestStandardizationStatement` (module
`Langlands.Global.AdelicEisensteinCuspidalTestStandardizationReduction`), is not among them: it
has the binders of `EisensteinCuspidalTestContinuedExpansionStatement` and supplies the two
standard-family instances below as existential witnesses in its conclusion.

- `F` is a number field and `G` an affine group scheme of finite type over `F`.
- `𝓕 : StandardParabolicFamily F G` is a standard parabolic family (module
  `Langlands.Global.AdelicLeadingCuspidalComponents`): standard parabolics `P_J = M_J U_J` with
  split components `A_J`, indexed by the subsets `J` of the simple relative roots of one maximal
  split torus `T` (`𝓕.i : T → G`) for one generic cocharacter. Its connected reductive hypothesis
  is part of the structure.
- Two instances are taken as binders of these three propositions: finiteness of the relative
  Weyl group of `T` (`Fintype (relativeWeylGroup 𝓕.i)`, a subsingleton) and the monomorphism
  property of the maps `𝓕.f J : A_J → T` (propositions). The root presentation
  `𝓕.rootPresentation J` of `P_J` (module `Langlands.Global.AdelicIntertwiningElementaryChainStatement`)
  is formed from the family and the index alone; the two instances are required by its root forms
  `rootFunctional` and its regularity predicate `IsRegularParameter`.
- `K` is a maximal compact subgroup of `G(𝔸)` in good position for `𝓕`: `P₀(𝔸) K = G(𝔸)` for the
  minimal standard parabolic `P₀ = 𝓕.p ⟨∅, _⟩` (named `h₀`), `K` is maximal compact, and
  `K ∩ M_J(𝔸)` is maximal compact in `M_J(𝔸)` for every standard `J`. Write
  `Kinf = K.comap (ofInfinite F G)`. For every standard `J`, the Iwasawa coverage
  `P_J(𝔸) K = G(𝔸)` is `𝓕.isIwasawaCompact_of_minimal h₀ J` (module
  `Langlands.Global.AdelicLeadingCuspidalInjectivityReduction`); it is used to form the Iwasawa
  heights, twists, Eisenstein series and intertwining integrals for `P_J`.
- `rho : MatrixRepresentation G (Fin N)` is a closed embedding and `hsmooth` a smooth structure of
  relative dimension `d`.
- Automorphy along `P_I` is `𝓕.IsAutomorphicOn hsmooth Kinf rho I`, automorphy on
  `U_I(𝔸) M_I(F) \ G(𝔸)`; cusp forms on `M_J(F) \ M_J(𝔸)` are `𝓕.IsLeviCuspForm Kinf rho J`.
- For a standard `I`, regularity of `λ ∈ X^*(P_I) ⊗ ℂ` is
  `(𝓕.rootPresentation I).IsRegularParameter hA hT R λ`, with
  `hA = (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1` and
  `hT = 𝓕.maximalSplit.isSplitSubtorus.1`: `R < B(Re λ|_{A_I}, α)` for every root `α` of `A_I` in
  `U_I` (module `Langlands.Global.AdelicEisensteinConvergenceStatement`). The root forms are
  `(𝓕.rootPresentation I).rootFunctional hA hT β : λ ↦ B(λ|_{A_I}, β)` and the roots of `A_I` in
  `U_I` are `(𝓕.rootPresentation I).unipotentRoots` (module
  `Langlands.Global.AdelicRootHyperplaneStatement`).
- The norm-one Levi test of a function `f` on `G(𝔸)` against `ψ` at `g` is
  `𝓕.leviPairing J (𝓕.constantTerm J f) g ψ`, that is
  `∫_{M_J(F) \ M_J(𝔸)^1} (C_J f)(m g) \overline{ψ(m)} dm`, where `C_J` is the constant term along
  `U_J`.

## `EisensteinCuspidalTestStandardExpansionStatement`

For every standard `I`, every `φ` automorphic along `P_I` and every standard `J` there are
`k : ℕ`, functions `Φ i` on `G(𝔸)`, complex linear maps `L i : X^*(P_I) ⊗ ℂ → X^*(P_J) ⊗ ℂ`,
scalar functions `c i` on `X^*(P_I) ⊗ ℂ` (`i : Fin k`) and a set `D` such that

1. every `c i` is meromorphic in linear coordinates with domain `D`
   (`IsMeromorphicInCoordinatesOn`);
2. every `c i` has poles along the hyperplanes of the root forms of the roots of `A_I` in `U_I`:
   `HasRootHyperplanePoles ((𝓕.rootPresentation I).rootFunctional hA hT)
   (𝓕.rootPresentation I).unipotentRoots (c i) D` (module
   `Langlands.Analysis.Meromorphic.RootHyperplanePoles`);
3. there is `R` such that for every `R`-regular `λ`, every cusp form `ψ` on `M_J(F) \ M_J(𝔸)` and
   every `g`,
   `𝓕.leviPairing J (𝓕.constantTerm J (E_{P_I}(φ, λ))) g ψ =
   ∑ i, c i λ * 𝓕.leviPairing J (𝓕.constantTerm J ([Φ i]_{L i λ})) g ψ`,
   where `E_{P_I}(φ, λ)` is `(𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries φ λ` and
   `[Φ]_μ` is the twist `(𝓕.isIwasawaCompact_of_minimal h₀ J).parameterTwist Φ μ` by the Iwasawa
   height of `P_J`.

This is `EisensteinCuspidalTestContinuedExpansionStatement` for the parabolic `P = P_I` with the
presentation `r = 𝓕.rootPresentation I`; the binders are arranged for this case.

## `EisensteinCuspidalTestIntertwiningExpansionStatement`

For every standard `I`, every `φ` automorphic along `P_I` and every standard `J` there are
`k : ℕ` and, for every `t : Fin k`,

- a standard index `I' t` and a morphism `f t : P_{I' t} → P_I` with
  `f t ≫ 𝓕.p I = 𝓕.p (I' t)` (so `P_{I' t} ⊆ P_I`);
- a rational point `n t ∈ normalizerPoints 𝓕.i` normalizing `T` and an isomorphism
  `c t : M_J → M_{I' t}` with `IsWeylConjugation (𝓕.p (I' t)) (𝓕.l (I' t)) (𝓕.p J) (𝓕.l J) (n t) (c t)`,
  that is `(n t)⁻¹ M_J (n t) = M_{I' t}` through `c t`: `(n t, c t)` presents an element of
  `W(P_{I' t}, P_J)` (module `Langlands.Global.AdelicIntertwiningOperator`);
- the positivity of the Weyl class `w_t` of `n t` on `I`: `w_t α` is a positive relative root for
  every `α ∈ I` (`schemeWeylCharacterAction`, which acts by `(w χ)(x) = χ(n⁻¹ x n)`);
- a retraction `π t : P_J → M_J` of the Levi (`𝓕.l J ≫ π t = 𝟙`);
- a function `φ' t` automorphic along `P_{I' t}`;

and `R` such that for every `R`-regular `λ ∈ X^*(P_I) ⊗ ℂ`, every cusp form `ψ` on
`M_J(F) \ M_J(𝔸)` and every `g`,

`𝓕.leviPairing J (𝓕.constantTerm J (E_{P_I}(φ, λ))) g ψ =
∑ t, 𝓕.leviPairing J (𝓕.constantTerm J ([M(n t, λ|) φ' t]_{(n t) λ})) g ψ`,

where `[M(n t, λ|) φ' t]_{(n t) λ}` is the intertwining integral
`(𝓕.isIwasawaCompact_of_minimal h₀ (I' t)).intertwiningIntegral (𝓕.iU (I' t)) (𝓕.iU J ≫ 𝓕.p J)
(n t) (φ' t) (parameterRestrict (f t) λ)`, the integral
`∫_{(U_J(F) ∩ n U_{I'}(𝔸) n⁻¹) \ U_J(𝔸)} (φ' t)_{λ|}(n⁻¹ v g) dv` of the twist of `φ' t` by the
restriction `λ|` of `λ` to `P_{I' t}` (`parameterRestrict`, module
`Langlands.Global.AdelicEisensteinConstantTermStatement`).

### Source and derivation

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math.
Soc. 37 (2024), 187–234 (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal
PDF and TeX `1911.02342.tex` in the registered folder):

- §6.7, p. 207 (TeX lines 1626–1665): `_Q W_P` represents `Q(F) \ G(F) / P(F)`; for
  `w ∈ _Q W_P`, `P_w` is the standard parabolic of `P` with Levi `M_P ∩ w⁻¹ M_Q w`; and
  `W^{⊃Q}(P) = {w : w M_P w⁻¹ ⊇ M_Q, wα > 0 for all α ∈ Δ_0^P} = {w ∈ _Q W_P : Q_w = Q}`, with
  `w ∈ W(P_w, Q)` for `w ∈ W^{⊃Q}(P)`;
- §6.10, Lemma with (6.17) and (6.18), p. 208 (TeX lines 1724–1760): for `λ` in the range of
  convergence, `C_{G,Q} E(φ, λ) = ∑_{w ∈ _Q W_P} E^Q(M(w, λ) C_{P,P_w} φ, wλ)` and
  `C^cusp_{G,Q} E(φ, λ) = ∑_{w ∈ W^{⊃Q}(P)} [M(w, λ) C_{P,P_w} φ]^cusp_{wλ}`, where `λ ∈ X^*(P)`
  is regarded as a parameter of `P_w` by restriction;
- §6.2, (6.8), p. 202: the cuspidal projection along `Q` is determined by the pairings with cusp
  forms on `M_Q(F) \ M_Q(𝔸)^1`.

The statement is derived from these items with `P = P_I` and `Q = P_J`; Bernstein–Lapid do not
state it separately. Testing (6.17) against a cusp form on `M_J`, the terms with `Q_w ≠ Q` are
Eisenstein series of `M_J` induced from proper parabolics and their tests vanish ((6.16) and the
definition of cusp forms), and for `w ∈ W^{⊃Q}(P)` the inner sum `E^Q` has the single term
`[M(w, λ) C_{P,P_w} φ]_{wλ}`. Its source parabolic is `P_w = P_{I'}` with `I' = I ∩ w⁻¹ J`, the
element `w` lies in `W(P_{I'}, P_J)` and is positive on `Δ_0^P = I`, and the inducing function is
`φ' = C_{P_I, P_{I'}} φ`, automorphic along `P_{I'}`. The exchange of the finite sum with the
pairing uses the absolute convergence of the pairings, which follows from the rapid decay of
cusp forms on `M_J(F) \ M_J(𝔸)^1` (Mœglin–Waldspurger I.2.18) and the moderate growth of the
terms. The statement keeps only what the reduction below uses: the functions `φ' t` are only
required to be automorphic along `P_{I' t}`, not to be the constant terms of `φ`.

## `IntertwiningRestrictedCuspidalTestContinuationStatement`

Let `I`, `I'`, `J` be standard indices, `f : P_{I'} → P_I` with `f ≫ 𝓕.p I = 𝓕.p I'`, `n` a
rational point normalizing `T` and `c : M_J → M_{I'}` with
`IsWeylConjugation (𝓕.p I') (𝓕.l I') (𝓕.p J) (𝓕.l J) n c`, `π : P_J → M_J` a retraction of the
Levi, and assume that the Weyl class of `n` maps every `α ∈ I` to a positive relative root. Let
`φ'` be automorphic along `P_{I'}`. Then there are `k : ℕ`, functions `Φ i` on `G(𝔸)`, scalar
functions `coeff i` on `X^*(P_I) ⊗ ℂ` and a set `D` such that

1. every `coeff i` is meromorphic in linear coordinates with domain `D`;
2. every `coeff i` has poles along the hyperplanes of the root forms of the roots of `A_I` in
   `U_I` (`HasRootHyperplanePoles` with `(𝓕.rootPresentation I).rootFunctional hA hT` and
   `(𝓕.rootPresentation I).unipotentRoots`);
3. there is `R` such that for every `R`-regular `λ ∈ X^*(P_I) ⊗ ℂ`, every cusp form `ψ` on
   `M_J(F) \ M_J(𝔸)` and every `g`,
   `𝓕.leviPairing J (𝓕.constantTerm J ([M(n, λ|) φ']_{nλ})) g ψ =
   ∑ i, coeff i λ * 𝓕.leviPairing J (𝓕.constantTerm J ([Φ i]_{nλ})) g ψ`.
   Here `[M(n, λ|) φ']_{nλ}` is the intertwining integral at `parameterRestrict f λ` as above,
   and `[Φ i]_{nλ}` is the twist by the height of `P_J` at
   `nλ = weylParameter (𝓕.l I') c π (parameterRestrict f λ)`, the parameter `w(λ|)` of
   `X^*(P_J) ⊗ ℂ` (module `Langlands.Global.AdelicIntertwiningOperator`).

The coefficients are functions of `λ ∈ X^*(P_I) ⊗ ℂ`, not of the parameter `λ|` of `P_{I'}`.

### Source and derivation

- Bernstein–Lapid §2.2, p. 191 (TeX lines 415–442): the integral defining `[M(w, λ)φ]_{wλ}`
  converges provided that `⟨Re λ, α^∨⟩ ≫ 0` for every root `α ∈ Φ_P` with `wα < 0`
  (Mœglin–Waldspurger II.1.6, pp. 87–88).
- Theorem 2.3 (3), p. 191 (TeX lines 444–500), with §8.5, pp. 224–225 (TeX lines 3417–3493): for
  `w ∈ W(P, Q)`, `λ ↦ M(w, λ)φ` takes values in a finite-dimensional space of automorphic forms
  along `Q` and continues meromorphically to `X^*(P) ⊗ ℂ`.
- §8.6, pp. 225–226 (TeX lines 3495–3530): the singularities of `M(w, λ)` are along hyperplanes
  `⟨λ, β^∨⟩ = c` with `β ∈ Φ_P` and `wβ < 0`; "it follows from (6.18) that the singularities of
  `E(φ, λ)` are also along root hyperplanes".

The statement is derived from these items and records the step of §8.6 that passes from (6.18)
to the singularities of `E(φ, λ)`; Bernstein–Lapid do not state it separately. Apply
Theorem 2.3 (3) and §8.6 to `w ∈ W(P_{I'}, P_J)`: `M(w, μ)φ' = ∑ i, a_i(μ) Φ_i` for
`μ ∈ X^*(P_{I'}) ⊗ ℂ`, with `Φ_i` automorphic along `P_J` and `a_i` meromorphic with singularities
along `⟨μ, β^∨⟩ = c`, `β ∈ Φ_{P_{I'}}`, `wβ < 0`. Since `w` is positive on `I`, it maps the
positive roots of `M_I` to positive roots, so every such `β` is a root in `U_I`, and on the
subspace `X^*(P_I) ⊗ ℂ` of restricted parameters the form `λ ↦ ⟨λ|, β^∨⟩` is a nonzero multiple of
the root form `λ ↦ B(λ|_{A_I}, β|_{A_I})` of the root `β|_{A_I}` of `A_I` in `U_I` (see the
Markdown of `AdelicRootHyperplaneStatement`). Hence `coeff i (λ) = a_i(λ|)` is meromorphic on
`X^*(P_I) ⊗ ℂ` with poles along root hyperplanes of `P_I`, and a power of the product of the forms
`λ ↦ B(λ - λ₀, β)` clears it near every `λ₀`, as in the Corollary of §8.6. For `λ` regular for
`P_I`, `⟨Re λ|, β^∨⟩` is large for every root `β ∈ Φ_{P_{I'}}` with `wβ < 0`, so the integral
defining `[M(w, λ|)φ']_{wλ}` converges by §2.2 and agrees there with the continuation. As `Φ_i` is
left `U_J(𝔸)`-invariant, `[M(w, λ|)φ']_{wλ} = ∑ i, a_i(λ|) [Φ_i]_{wλ}` and its constant term along
`P_J` is itself; the tests are linear because the pairings converge absolutely (rapid decay of
cusp forms, Mœglin–Waldspurger I.2.18).

The Library's `IntertwiningMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicIntertwiningContinuationStatement`) and
`IntertwiningRootHyperplaneContinuationStatement` (module
`Langlands.Global.AdelicRootHyperplaneContinuationStatement`) are stated for parameters `μ` of
the source parabolic `P_{I'}`.

- `IntertwiningMeromorphicContinuationStatement` gives finitely many automorphic forms `ψ i` along
  the target parabolic and coefficients `coeff i` meromorphic in linear coordinates, with
  `M(w, μ)φ' = ∑ i, coeff i μ • ψ i` for `μ` sufficiently regular for `P_{I'}`. It says nothing
  about the location of the poles.
- `IntertwiningRootHyperplaneContinuationStatement` gives finitely many functions `ψ i` on `G(𝔸)`
  (no automorphy is asserted) and coefficients `coeff i` meromorphic in linear coordinates with one
  domain, with `M(w, μ)φ' g = ∑ i, coeff i μ * ψ i g` for `μ` sufficiently regular for `P_{I'}`,
  and, near every point, the local clearing of the expanded value `∑ i, coeff i μ * ψ i g` by a
  power of the product of the root forms of a finite set of roots of `A_{I'}` in `U_{I'}`.

When `I' ⊊ I` there are roots of `A_{I'}` in `M_I ∩ U_{I'}`, and their root forms vanish on the
restricted parameters `λ|`, `λ ∈ X^*(P_I) ⊗ ℂ`. Regularity is a strict lower bound on the root
forms, so no restricted parameter is `R`-regular for `P_{I'}` when `R ≥ 0`; and a clearing product
that contains one of these forms vanishes identically on the restricted parameters, so it gives no
information there. (When `I' = I` and `f` is the identity, for instance for the identity element
of `W^{⊃P}(P)`, restriction is the identity and preserves regularity.) For this reason the present
statement is formulated directly in the parameters of `P_I`, with poles allowed along the root
hyperplanes of `P_I`. For `w` positive on `I` no root of `M_I` is inverted, so the restrictions of
the hyperplanes of the roots inverted by `w` (§8.6) lie among these root hyperplanes of `P_I`; the
inclusion may be strict (for the identity element the set of inverted roots is empty).

## The reduction

`eisensteinCuspidalTestStandardExpansionReduction` takes the two premises and the data of the
standard expansion.

1. The tested constant-term formula, applied to `I`, `φ` and `J`, gives `k`, `I'`, `f`, `n`, `c`,
   `π`, `φ'`, their properties and a bound `R₀`.
2. The restricted continuation, applied for each `t : Fin k` to `I`, `I' t`, `J`, `f t`, `n t`,
   `c t`, `π t` and `φ' t` with the properties from step 1, gives `m t`, `Φ t`, `coeff t`, `D t`
   and a bound `R t` (`choose`).
3. The terms are indexed by the finite type `κ = Σ t, Fin (m t)`, enumerated by
   `Fintype.equivFin`. For the index `i` corresponding to `(t, j)` the expansion uses
   `Φ t j`, the linear map `weylParameter (𝓕.l (I' t)) (c t) (π t) ∘ₗ parameterRestrict (f t)` and
   the coefficient `coeff t j`.
4. The common domain is `Dc = ⋂_{(t, j) ∈ κ} D t`. Each `D t` with `m t > 0` is the domain of some
   `coeff t j`, hence open and dense in coordinates, and so is the finite intersection
   (`isOpenDenseInCoordinates_iInter_of_finite`). Meromorphy with domain `Dc` follows by
   `IsMeromorphicInCoordinatesOn.congr_mono` and the pole condition by
   `HasRootHyperplanePoles.mono`.
5. The bound is `max R₀ 0 + ∑ t, |R t|`, which is at least `R₀` and every `R t`
   (`le_max_zero_add_sum_abs`); `ParabolicRootPresentation.IsRegularParameter.mono` (module
   `Langlands.Global.AdelicRootHyperplaneReduction`) lowers the bound of regularity. For a regular
   `λ`, step 1 writes the test of `C_J E_{P_I}(φ, λ)` as the sum over `t` of the tests of the
   intertwining terms, step 2 expands each of them, and `Fintype.sum_sigma` and `Equiv.sum_comp`
   rewrite the double sum as a sum over `Fin (Fintype.card κ)`.

## Scope

Only the number field case is stated. The module proves the implication and the inequality
`le_max_zero_add_sum_abs`; it does not prove the three premises.
