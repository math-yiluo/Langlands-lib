# Proposition II.4.5 from the lemmas it uses

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermInd`, and through it
`ConstantTerm`. From `ConstantTerm` it uses `ConstantTermEstimate` (the estimate of
Proposition II.4.5, which `ConstantTerm` takes as a hypothesis) and `conjUnipotent`.
From `ConstantTermInd` it uses `IsConjModulus` and `conjUnipotentHomeomorph`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Proposition II.4.5, printed pp. 262–263 (PDF pp. 28–29). Let `P = M U` be a standard
  parabolic subgroup. For every `d ∈ ℕ` there are `d' ∈ ℕ` and `c > 0` such that, for
  every `m ∈ M`,

  `δ_P(m)^{-1/2} ∫_Ū Ξ(m ū) (1 + σ(m ū))^{-d'} dū ≤ c Ξ^M(m) (1 + σ(m))^{-d}`.

  The remark after the proof says that the proposition also holds for semi-standard `P`.
- The proof of II.4.5 uses:
  - the Cartan decomposition of `M`, `M = (K ∩ M) M̄^{M+}_0 (K ∩ M)` (I.1 (4), printed
    p. 241, PDF p. 7, applied to `M`), to reduce to `m ∈ M̄^{M+}_0`;
  - Lemma II.4.4 (printed p. 262, PDF p. 28): there are `d ∈ ℕ` and `c > 0` with
    `Ξ(m ū) ≤ c δ_0(m)^{1/2} δ_0(m_0(ū))^{1/2} (1 + σ(m ū))^d` for `m ∈ M_0` and
    `ū ∈ Ū`;
  - Lemma II.3.1 (printed pp. 254–255, PDF pp. 20–21): for a semi-standard
    `P = M U` there are `C_1, C_2 > 0` with
    `C_1 (1 + σ(m u)) ≤ 1 + sup(σ(m), σ(u)) ≤ C_2 (1 + σ(m u))` for `m ∈ M`, `u ∈ U`.
    The proof of II.4.5 uses the second inequality for the opposite parabolic subgroup
    `P̄ = M Ū`;
  - the elementary inequality `1 + sup(a, b) ≥ (1 + a)^{1/2} (1 + b)^{1/2}`;
  - Lemma II.1.1 (printed p. 251, PDF p. 17) for `M`: `C_1 δ^M_0(m)^{1/2} ≤ Ξ^M(m)` for
    `m ∈ M̄^{M+}_0`, together with `δ_0(m)^{1/2} δ_P(m)^{-1/2} = δ^M_0(m)^{1/2}`;
  - Lemma II.4.2 (printed p. 261, PDF p. 27): for some `d ∈ ℕ` the integral
    `∫_Ū δ_0(m_0(ū))^{1/2} (1 + σ(ū))^{-d} dū` converges.

## Scope: abstract data and explicit hypotheses

The reductive group, its parabolic subgroups, `K`, the Haar measures and the modulus
characters are not constructed here, as in `ConstantTerm` and `ConstantTermInd`. The
module works with:

- a topological group `G` with its Borel σ-algebra;
- subgroups `M` and `U` of `G` with `hMU : M ≤ Subgroup.normalizer U`, a measure `ν` on
  `U` and a character `δ : M →* ℝ≥0ˣ`. In the application `U` is Waldspurger's `Ū`,
  `ν` is its Haar measure `dū`, and `δ` is the modulus character of `P̄ = M Ū`, that is
  `δ_P^{-1}` on `M`. Then `δ(m)^{1/2} = δ_P(m)^{-1/2}`, and the published
  `ConstantTermEstimate ν δ Ξ σ ΞM σM` is the inequality of II.4.5, with real instead
  of integer exponents. The identification of `δ` with `δ_P^{-1}` is not made here;
- functions `Ξ, σ : G → ℝ` and `ΞM : M → ℝ` (Waldspurger's `Ξ`, `σ` and `Ξ^M`). As in
  the article, the height function on `M` is the restriction of `σ`: the conclusion is
  `ConstantTermEstimate ν δ Ξ σ ΞM (fun m => σ m)`;
- a subgroup `KM` of `M` (Waldspurger's `K ∩ M`) and a set `S ⊆ M` (his `M̄^{M+}_0`);
- functions `e, eM : M → ℝ` and `w : U → ℝ`. In the application `e(m) = δ_0(m)^{1/2}`,
  `eM(m) = δ^M_0(m)^{1/2}` and `w(ū) = δ_0(m_0(ū))^{1/2}`.

None of the ingredients of the proof is proved here for Waldspurger's data. Each is a
hypothesis of `constantTermEstimate_of_bounds`, stated as one of the Prop-valued
definitions below or as an explicit inequality.

## Definitions

- `IsDoubleCosetCover K S : Prop`, for a subgroup `K` and a set `S` of a group `H`:
  every `h ∈ H` is `k₁ s k₂` with `k₁, k₂ ∈ K` and `s ∈ S`. For `H = M`, `K = K ∩ M` and
  `S = M̄^{M+}_0` this is the covering half of the Cartan decomposition of `M`;
  disjointness is not needed and not included.
- `XiLowerBound Ξ S e : Prop`, for functions `Ξ, e : X → ℝ` and `S ⊆ X`: there is a
  real `C` with `e(x) ≤ C Ξ(x)` for all `x ∈ S`. With `X = M`, `Ξ = Ξ^M`,
  `S = M̄^{M+}_0` and `e = (δ^M_0)^{1/2}` this is the lower bound of Lemma II.1.1 for
  `M`. The constant is not required to be positive.
- `UnipotentXiBound Ξ σ S e w : Prop`: there are real `D` and `c` with
  `Ξ(m u) ≤ c e(m) w(u) (1 + σ(m u))^D` for all `m ∈ S` and `u ∈ U`. With
  `e = δ_0^{1/2}`, `w(ū) = δ_0(m_0(ū))^{1/2}` and `S ⊆ M_0` this is Lemma II.4.4 on
  `S`. The exponent is a real number (Waldspurger's `d ∈ ℕ` is a special case).
- `SigmaProductBound M U σ : Prop`: there is `C > 0` with
  `C (1 + max(σ(m), σ(u))) ≤ 1 + σ(m u)` for all `m ∈ M` and `u ∈ U`. This is the
  second inequality of Lemma II.3.1 (with `C = C_2^{-1}`), for the pair `(M, U)`.
- `UnipotentWeightIntegrable ν w σ : Prop`: for some real `d`,
  `∫⁻_U ofReal(w(u) (1 + σ(u))^{-d}) dν(u) < ∞`. With `w(ū) = δ_0(m_0(ū))^{1/2}` this
  is Lemma II.4.2.

Real exponents are used throughout, as in `Basic` and `ConstantTerm`. Integrals of
nonnegative functions are lower Lebesgue integrals `∫⁻` of `ENNReal.ofReal` of the
integrand, as in `ConstantTermEstimate`.

## Results

- `IsConjModulus.lintegral_comp`: under `IsConjModulus hMU ν δ`, for every `m ∈ M` and
  `φ : U → ℝ≥0∞`, `∫⁻_U φ(m u m⁻¹) dν(u) = δ(m)⁻¹ ∫⁻_U φ dν`. It is the lower-integral
  form of `IsConjModulus.integral_comp` of `ConstantTermInd`.
- `one_add_rpow_neg_le`: for real `a, b ≥ 0`, `C > 0`, `r ≥ 0` and `t`, if
  `C (1 + max(a, b)) ≤ 1 + t`, then
  `(1 + t)^{-2r} ≤ C^{-2r} (1 + a)^{-r} (1 + b)^{-r}`.
- `constantTermEstimate_of_bounds` (Proposition II.4.5). Assume:
  - `hν : IsConjModulus hMU ν δ` and `hδK : δ(k) = 1` for `k ∈ KM`;
  - `hcover : IsDoubleCosetCover KM S`;
  - `Ξ` and `σ` satisfy `Ξ(k₁ g k₂) = Ξ(g)` and `σ(k₁ g k₂) = σ(g)` for `k₁, k₂ ∈ KM`
    and `g ∈ G`, and `ΞM(k₁ m k₂) = ΞM(m)` for `k₁, k₂ ∈ KM` and `m ∈ M`;
  - `σ ≥ 0` on `G`, `ΞM ≥ 0` on `M`, `e ≥ 0` on `S`, `w ≥ 0` on `U`;
  - `e(m) δ(m)^{1/2} ≤ eM(m)` for `m ∈ S`;
  - `UnipotentXiBound Ξ σ S e w`, `SigmaProductBound M U σ`, `XiLowerBound ΞM S eM` and
    `UnipotentWeightIntegrable ν w σ`.

  Then `ConstantTermEstimate ν δ Ξ σ ΞM (fun m => σ m)`: for every real `d` there are a
  real `d'` and `c ≥ 0` with
  `δ(m)^{1/2} ∫⁻_U ofReal(Ξ(m u) (1 + σ(m u))^{-d'}) dν(u) ≤ c ofReal(ΞM(m) (1 + σ(m))^{-d})`
  for every `m ∈ M`.

For Waldspurger's data the hypotheses correspond to the ingredients listed under Source:
`hcover` to the Cartan decomposition of `M`; `UnipotentXiBound` to Lemma II.4.4 (on
`M̄^{M+}_0 ⊆ M_0`); `SigmaProductBound` to Lemma II.3.1 for `P̄`; `XiLowerBound` to
Lemma II.1.1 for `M`, and the inequality `e δ^{1/2} ≤ eM` to the identity
`δ_0 δ_P^{-1} = δ^M_0` on `M_0`; `UnipotentWeightIntegrable` to Lemma II.4.2. The
invariance of `Ξ`, `σ` and `Ξ^M` comes from Lemma II.1.1 and I.1. `IsConjModulus`
holds for a regular Haar measure and the Haar modulus `HaarModulus.restrictCharacter`
(`isConjModulus_restrictCharacter` in `ConstantTermInd`), and that character is trivial
on compact subgroups (`eq_one_of_isOpen_ker_of_isCompact`); the identification of the
Haar modulus with `δ_P^{-1}` and the other ingredients are open for Waldspurger's data.

## Proof notes

The proof follows Waldspurger's.

- Constants. Lemma II.4.4 gives `D` and `c₁`, Lemma II.3.1 gives `C₂ > 0`, Lemma II.1.1
  gives `C₃`, and Lemma II.4.2 gives an exponent `d₂`. Given `d`, put
  `r = max(d, d₂, 0)` and `d' = D + 2r`; then `-(D - d') / 2 = r` dominates both `d`
  and `d₂`. Waldspurger takes `d'` large enough; this is an explicit choice. The
  constants `c₁` and `C₃` are replaced by `max(c₁, 0)` and `max(C₃, 0)`.
- Points of `S`. For `s ∈ S` and `u ∈ U`, Lemma II.4.4 gives
  `Ξ(s u) (1 + σ(s u))^{-d'} ≤ c₁ e(s) w(u) (1 + σ(s u))^{-2r}`. Lemma II.3.1 and
  `one_add_rpow_neg_le` bound `(1 + σ(s u))^{-2r}` by
  `C₂^{-2r} (1 + σ(s))^{-r} (1 + σ(u))^{-r}`. Integrating over `U` gives at most
  `c₁ C₂^{-2r} e(s) (1 + σ(s))^{-r} I`, where
  `I = ∫⁻_U ofReal(w(u) (1 + σ(u))^{-r}) dν`. `I` is finite by Lemma II.4.2, because
  `(1 + σ(u))^{-r} ≤ (1 + σ(u))^{-d₂}`. Multiplying by `δ(s)^{1/2}`, the inequality
  `e(s) δ(s)^{1/2} ≤ eM(s) ≤ C₃ Ξ^M(s)` and `(1 + σ(s))^{-r} ≤ (1 + σ(s))^{-d}` give
  the estimate at `s` with `c = max(c₁, 0) C₂^{-2r} max(C₃, 0) I`.
- Reduction to `S`. Write `m = k₁ s k₂` (`hcover`). Then `δ(m) = δ(s)`,
  `m u = k₁ (s (k₂ u k₂⁻¹)) k₂`, so the integrand at `m` is the integrand at `s`
  composed with `u ↦ k₂ u k₂⁻¹`. By `IsConjModulus.lintegral_comp` and `δ(k₂) = 1`,
  the two integrals are equal. The right side is unchanged because `Ξ^M` and `σ` are
  bi-invariant. Waldspurger states this reduction in one sentence ("On peut se limiter
  à démontrer l'inégalité de l'énoncé pour `m ∈ M̄^{M+}_0`").

## Open obligations

For Waldspurger's `G`, Proposition II.4.5 still needs: the Cartan decomposition of `M`;
Lemma II.4.4 (from Lemma II.1.1, the Cartan decomposition of `G` and Lemma II.3.2);
Lemma II.3.1 (from the algebraic embedding `τ` of I.1); both bounds of Lemma II.1.1
(the upper one uses Proposition I.4.3, Casselman's asymptotics); Lemma II.4.2 (its proof
cites Lemmas II.3.4, II.4.1 and II.3.3); the identities between `δ_0`, `δ^M_0` and `δ_P`; and
the identification of the Haar modulus with `δ_P^{-1}`. None of these is proved in
this module.
