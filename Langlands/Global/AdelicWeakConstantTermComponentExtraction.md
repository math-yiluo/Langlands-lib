# Levi pairings with the components of a weak constant term

This module reduces the absolute convergence of the Levi pairing (3.7) of Delorme with a single
unitary component of a constant-term decomposition (3.2) to the absolute convergence of the
same pairing with the whole weak constant term. The reduction is algebraic: a component is a
polynomial in one translation by the positive split component applied to the weak constant
term, and the pairing with a translate is a nonzero multiple of the pairing at a translated
split-component point.

It contains:

- `AdelicGroupPoints.characterLog_pow` and `AdelicGroupPoints.parameterPower_pow`:
  `H(x^k) = k H(x)` and `(x^k)^λ = (x^λ)^k` on actual adelic points;
- `StandardParabolicFamily.splitComponentEquivariant_apply`: a split-component equivariant
  function satisfies `φ(x g) = δ_P(x)^{1/2} φ(g)` for `x` in the positive split component;
- `StandardParabolicFamily.exists_positiveSplitComponent_parameterPower_ne`: a separating point
  of the positive split component for finitely many complex parameters;
- `StandardParabolicFamily.positivePairingIntegrable` with
  `positivePairingIntegrable_translate` and `positivePairingIntegrable_aeval`;
- `StandardParabolicFamily.pairingIntegrable_component_of_sum`: the extraction of a component;
- the proposition `WeakConstantTermPairingIntegrableStatement`, which is stated and not proved
  here;
- `weakConstantTermComponentPairingIntegrable_of_weakConstantTerm`: this proposition implies
  `WeakConstantTermComponentPairingIntegrableStatement` of the module
  `Langlands.Global.AdelicWeakConstantTermPairingPolynomials`.

All theorems of the module use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023), 109107,
registered as `delorme-2023-spectral-theorem-langlands` (published PDF, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`):

- (3.2), p. 10: the decomposition `φ(g) = ∑_{λ ∈ E_P(φ)} e^{λ(H_P(g))} φ_{0,λ}(g)` of an
  automorphic form on `[G]_P` by its exponents, with `φ_{0,λ} ∈ S(𝔞_P^*) ⊗ A^n_P(G)`;
- Definition 3.7, p. 13: the weak constant term `φ_P^w`, the sum of the terms of (3.2) for
  `φ_P` with unitary exponents;
- Lemma 3.8 (ii), p. 14: `φ_P^w ∈ A_P^{temp}(G)` for tempered `φ`;
- §3.4, p. 15, (3.7) and Remark 3.9: for `φ ∈ A^2_P(G)` and `ψ ∈ A_P^{temp}(G)` the integral
  `∫_{M(𝔸)^1 × K} φ(exp_P X m k) conj ψ(exp_P X m k) dm dk` converges absolutely. The source
  deduces this from `A^2(G) ⊂ C(G)` (Mœglin–Waldspurger, *Spectral Decomposition and
  Eisenstein Series*, 1995, Lemmas I.4.1 and I.4.11), (2.10) and Proposition 3.5.

The Lean objects are those of `Langlands.Global.AdelicTemperedVanishingReduction`:
`IsAutomorphicExponentDecomposition` is (3.2), `unitaryExponentSum` and `IsWeakConstantTerm`
give Definition 3.7, and `squareIntegrablePairingIntegrand` with
`squareIntegrablePairingMeasure` is the integrand and measure of (3.7) on
`K × M(F) \ M(𝔸)^1` without the nonzero factor `e^{-2ρ_P(X)}` (see that module's Markdown for
the correspondence).

## The proposition `WeakConstantTermPairingIntegrableStatement`

Fix a number field `F`, a connected reductive `G`, a maximal compact subgroup `K ⊆ G(𝔸)`, a
closed matrix embedding `rho`, the calculus data `hsmooth` and `hcalc`, and a compatible family
`𝓕` of standard parabolics with `hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K`, that is
`P_∅(𝔸) K = G(𝔸)`. These are the hypotheses of `WeakConstantTermComponentPairingIntegrableStatement`
and of `WavePacketWeakConstantTermOrthogonalityStatement`. Let `Φ` satisfy
`IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ`, let `J` be a standard index
and let `ψ` satisfy

`𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ`,

so `ψ = Φ_P^w` for `P = P_J`. For every `φ` with
`IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ`
(Lapid's `A^2_P` for this `K`) and every `x ∈ 𝓕.positiveSplitComponent J`, the proposition
asserts that `𝓕.squareIntegrablePairingIntegrand K J x φ ψ` is integrable for
`𝓕.squareIntegrablePairingMeasure K hK.isCompact J`, the product of the Haar probability of `K`
and the quotient Haar measure on `M(F) \ M(𝔸)^1`.

Correspondence. This is the absolute convergence of (3.7) for `ψ = Φ_P^w`, which is tempered by
Lemma 3.8 (ii) once `Φ` is tempered (Proposition 3.5). It is the integrability part of
`IsSquareIntegrableOrthogonal` for the weak constant terms of `Φ`. As in the target, `K` ranges
over all maximal compact subgroups with `P_∅(𝔸) K = G(𝔸)`, not only those in good position used
by Delorme (see "The compact subgroup" in the Markdown of
`Langlands.Global.AdelicTemperedVanishingReduction`); the pairing uses the integrand, the measure
and the space `A^2_P` of this `K`.

## Proof of the extraction

### Separating point

`exists_positiveSplitComponent_parameterPower_ne`: given `λ` and a finite set `s` of complex
parameters of `P` not containing `λ`, there is `a` in the positive split component with
`a^μ ≠ a^λ` for every `μ ∈ s`.

Proof (as implemented). Suppose not. For `μ ∈ s` let `B_μ` be the kernel of the character
`a ↦ a^{μ - λ}` of the positive split component `𝔄_P` (`parameterCharacter`). Since
`a^μ = a^{μ - λ} a^λ` and `a^λ ≠ 0`, the hypothesis says that the `B_μ` cover `𝔄_P`. By
B. H. Neumann's lemma (`Subgroup.exists_finiteIndex_of_leftCoset_cover`) some `B_μ` has finite
index `n ≠ 0`, so `(a^n)^{μ - λ} = 1` for every `a` (`Subgroup.pow_index_mem`,
`parameterPower_pow`). The published `eisensteinPositiveParameters`, applied to the parabolic
root presentation of `P_J`, says that `characterLog` maps `𝔄_P` onto the real character dual
and that `λ ↦ (a ↦ a^λ)` is injective on `𝔄_P`. Given `a`, choose `b` with
`H(b) = n⁻¹ H(a)`; then `H(b^n) = H(a)` (`characterLog_pow`), and since `a^ν` depends only on
`H(a)`, `a^{μ - λ} = (b^n)^{μ - λ} = 1 = a^0`. Injectivity gives `μ = λ`, contradicting
`λ ∉ s`.

### Translations and polynomials in a translation

`positivePairingIntegrable J K meas φ` is the complex subspace of functions `ψ` on `G(𝔸)` such
that the pairing integrand of `φ` and `ψ` is integrable for the measure `meas` at every point of
`𝔄_P`. It is a subspace because the integrand is additive and conjugate-linear in `ψ`.

`positivePairingIntegrable_translate`: if `φ` is split-component equivariant
(`IsSplitComponentEquivariant (𝓕.p J) (𝓕.l J) φ`, the condition defining `A^n_P`) and
`a ∈ 𝔄_P`, the subspace is stable under the translation `ψ ↦ ψ(a ·)`
(`splitComponentRepresentation`). Proof: with `y = m k`,
`φ(a x y) = δ_P(a)^{1/2} φ(x y)` (`splitComponentEquivariant_apply`: a point of `𝔄_P` is the image of a positive point `t`
of the split torus, whose image in `M(𝔸)` lies in
`RestrictionSplitCentre.canonicalSubgroup` by `imageSubgroup_eq_canonicalSubgroup`, where
`IsSplitComponentEquivariant` applies), so the integrand of `φ` and `ψ(a ·)` at `x` is
`δ_P(a)^{-1/2}` times the integrand of `φ` and `ψ` at `a x ∈ 𝔄_P`.

`positivePairingIntegrable_aeval`: the subspace is stable under `q(T)` for every complex
polynomial `q` and the translation `T` by `a`, by `aeval_eq_sum_range` and induction on powers.

### Extraction

`pairingIntegrable_component_of_sum`: let `φ` be split-component equivariant, let `s` be a
finite set of complex parameters, let `c μ` have normalized exponent `μ`
(`HasExponent J μ (c μ)`) for `μ ∈ s`, and suppose that the pairing of `φ` with
`∑_{μ ∈ s} c μ` is integrable at every point of `𝔄_P` (for any measure `meas`). Then for every
`λ ∈ s` the pairing of `φ` with `c λ` is integrable at every point of `𝔄_P`.

Proof (as implemented). Let `ρ = ρ_P`. The separating point applied to `λ + ρ` and the shifted
set `{μ + ρ : μ ∈ s, μ ≠ λ}` gives `a ∈ 𝔄_P` with `α_μ ≠ α_λ` for `μ ≠ λ`, where
`α_μ = a^{μ + ρ}`. Let `T` be the translation by `a`. The unnormalized exponent of `c μ` is
`μ + ρ` (`hasExponent_iff`), so `c μ` lies in the joint generalized eigenspace of the
translations for the character `b ↦ b^{μ + ρ}`
(`mem_jointGenEigenspace_of_hasUnnormalizedExponent`), and some power `(T - α_μ)^{k_μ}` kills
`c μ`. Put `L = (X - α_λ)^{k_λ}` and `R = ∏_{μ ∈ s, μ ≠ λ} (X - α_μ)^{k_μ}`. These polynomials
are coprime, since the `α_μ` with `μ ≠ λ` differ from `α_λ`
(`isCoprime_X_sub_C_of_isUnit_sub`, `IsCoprime.pow`, `IsCoprime.prod_right`), so
`u L + v R = 1` for some `u`, `v`. Then `(vR)(T)` kills `c μ` for `μ ≠ λ` (the factor for `μ`
divides `R`) and fixes `c λ` (`(vR)(T) = 1 - u(T) L(T)` and `L(T)` kills `c λ`). Hence
`c λ = (vR)(T) ∑_{μ ∈ s} c μ`, and `positivePairingIntegrable_aeval` gives the claim.

## Proof of the reduction

`weakConstantTermComponentPairingIntegrable_of_weakConstantTerm` proves
`WeakConstantTermComponentPairingIntegrableStatement` from
`WeakConstantTermPairingIntegrableStatement`.

Proof (as implemented). Take the data of the target: `Φ`, the decomposition `(s, c)` of
`𝓕.constantTerm J Φ` with `IsAutomorphicExponentDecomposition`, `λ ∈ s` with
`parameterRealPart λ = 0`, and `φ` with `IsSquareIntegrableInducedForm`. The function
`𝓕.unitaryExponentSum J s c` is a weak constant term of `Φ`, witnessed by the same `(s, c)`.
The proposition gives integrability of the pairing of `φ` with this sum at every point of
`𝔄_P`. The sum runs over the unitary members of `s`, each with a normalized exponent
(`IsAutomorphicExponentDecomposition.exponent`), and `λ` is one of them. The inducing form is
split-component equivariant (second conjunct of `IsSquareIntegrableInducedForm`), so
`pairingIntegrable_component_of_sum` gives integrability of the pairing with `c λ`, for the same
`K`, the same measure and every point of `𝔄_P`.

## Scope

The extraction and the reduction are proved here. `WeakConstantTermPairingIntegrableStatement`
is not proved in this module. Delorme's route to it uses the temperedness of `Φ_P^w`
(Proposition 3.5 and Lemma 3.8 (ii)), the inclusion of square-integrable automorphic forms of
the Levi subgroup in the Schwartz space (Mœglin–Waldspurger I.4.1 and I.4.11), and the
integrability of the product of the two bounds over `M(F) \ M(𝔸)^1` ((2.10) for the Levi
subgroup), all for the given compact subgroup `K`.
