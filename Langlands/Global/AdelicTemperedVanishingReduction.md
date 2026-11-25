# Reduction of `TemperedWavePacketVanishingStatement` to three ingredients

Module `Langlands.Global.AdelicTemperedVanishingReduction` splits the last step of Delorme's
proof of the completeness of wave packets, the published
`Langlands.Global.TemperedWavePacketVanishingStatement`, into three propositions. It proves that
the three together imply that statement, and it proves the first of them, so the target follows
from the remaining two. The split is along Delorme's weak constant terms (Definition 3.7). In
short:

- `MinimalParabolicStandardFamilyStatement` (structure theory): every minimal parabolic of a
  connected reductive group over a number field is the minimal member `P_∅` of a compatible
  family of standard parabolics.
- `WavePacketWeakConstantTermOrthogonalityStatement` (Delorme §§4–7): if an automorphic form of
  Lemma 7.10 is orthogonal to every wave packet, then each of its weak constant terms `Φ_P^w`
  satisfies the condition defining `𝒜^{temp,c}_P(G)`.
- `TemperedWeakConstantTermVanishingStatement` (Delorme §3): an automorphic form of Lemma 7.10
  all of whose weak constant terms satisfy that condition is zero.

| Declaration | Kind | Source |
| --- | --- | --- |
| `StandardParabolicFamily.bot` | definition | the index `∅` of `P_∅` |
| `StandardParabolicFamily.IsAutomorphicExponentDecomposition` | definition | Delorme (3.2); MW I.3.2 |
| `StandardParabolicFamily.unitaryExponentSum` | definition | Delorme Definition 3.7 |
| `StandardParabolicFamily.IsWeakConstantTerm` | definition | Delorme Definition 3.7 |
| `StandardParabolicFamily.squareIntegrablePairingIntegrand` | definition | Delorme (3.7) |
| `StandardParabolicFamily.squareIntegrablePairingMeasure` | definition | Delorme (3.7) |
| `StandardParabolicFamily.IsSquareIntegrableOrthogonal` | definition | Delorme, definition of `𝒜^{temp,c}_P(G)` after (3.7) |
| `MinimalParabolicStandardFamilyStatement` | statement | Borel–Tits; Library structure theory |
| `minimalParabolicStandardFamily` | theorem (proved) | proof of `MinimalParabolicStandardFamilyStatement` |
| `WavePacketWeakConstantTermOrthogonalityStatement` | statement | Delorme Theorem 7.1, Proposition 7.8, Lemma 7.11, end of the proof of Theorem 7.9 |
| `TemperedWeakConstantTermVanishingStatement` | statement | Delorme Propositions 3.5, 3.6, Definition 3.7, Lemmas 3.8, 3.10 (ii) |
| `temperedWavePacketVanishing_of_reduction` | theorem (proved) | Delorme, end of the proof of Theorem 7.9 |
| `temperedWavePacketVanishing_of_weakConstantTerms` | theorem (proved) | the reduction with the first ingredient discharged |

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023)
  109107, registered as `delorme-2023-spectral-theorem-langlands`. The folder holds the published
  PDF and the arXiv TeX 2006.12893. The numbering below is that of the published PDF, whose page
  numbers are the PDF page numbers. (The arXiv TeX numbers some displays differently.)
  - p.10, (3.2): every `φ ∈ A_P(G)` can be written uniquely as
    `φ(g) = ∑_{λ ∈ E_P(φ)} e^{λ(H_P(g))} φ_{0,λ}(g)` with `E_P(φ) ⊂ 𝔞_{P,ℂ}^*` and
    `φ_{0,λ}` a nonzero element of `S(𝔞_P^*) ⊗ A^n_P(G)`; the space `A^2_P(G)`;
  - p.11: Lemma 3.2 and Definition 3.3 (tempered automorphic forms);
  - p.12: Proposition 3.5 (for `φ ∈ 𝒜(G)`, tempered ⇔ `[G]`-tempered);
  - p.13: Proposition 3.6 (`φ` is tempered if and only if the exponents of its constant terms
    along all standard parabolics are subunitary) and Definition 3.7 ("the weak constant term of
    `φ`, denoted `φ_P^w`, as the sum of the terms for `φ_P` in (3.2) corresponding to unitary
    exponents");
  - p.14: Lemma 3.8 (in particular (ii): `φ_P^w ∈ A_P^{temp}(G)`);
  - p.15, (3.7): for `φ ∈ A^2_P(G)` and `ψ ∈ A_P^{temp}(G)`,
    `(φ, ψ)^X_P = e^{-2ρ_P(X)} ∫_{M(𝔸)^1 × K} φ(exp_P X m_1 k) conj ψ(exp_P X m_1 k) dm_1 dk`,
    an absolutely convergent integral and an exponential polynomial `p_P(φ, ψ)` in `X ∈ 𝔞_P`;
    "We denote by `𝒜^{temp,c}(G)` the space of `ψ ∈ 𝒜^{temp}(G)` such that for all
    `φ ∈ 𝒜^2(G)`, the polynomial `p_G(φ, ψ)` is zero. We define similarly `𝒜_P^{temp,c}(G)`";
    Lemma 3.10 (ii): "If `φ ∈ 𝒜^{temp}(G)` and `φ_Q^w ∈ 𝒜_Q^{temp,c}(G)` for all standard
    parabolic subgroup `Q` of `G`, then `φ = 0`";
  - Theorem 7.1 (§7, truncation of `Ω^T` versus `ω^T`);
  - pp.33–35: Proposition 7.8, Theorem 7.9, the preliminary remark after it, Lemma 7.10,
    Lemma 7.11 (`I = C_P ∑_{μ ∈ E^w_P(Φ)} [(p_P(φ, Φ_{P,0,μ})^0(∂) a_1)](μ|_{𝔞_P^G})`), and the
    end of the proof: "One concludes, by varying `a_1`, `a_2` and `φ`, that
    `Φ_{P,0,μ} ∈ 𝒜_P^{temp,c}(G)` for all `P` and `μ ∈ E^w_P(Φ)`. Then, using Lemma 3.10 (ii),
    one concludes that `Φ = 0`."
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.3.1 (p.41: every smooth
  `𝔷(A_M)`-finite function on `A_M` is a linear combination of `a ↦ a^λ Q(log_M a)`) and the
  Lemma of I.3.2 (p.41: `ℂ[Re 𝔞_M] ⊗ A(U(𝔸)M(k)\G)_Z → A(U(𝔸)M(k)\G)` is an isomorphism; its
  proof decomposes an automorphic form on `U(𝔸)M(k) \ G` by its exponents along `A_M`, with
  automorphic components).
- Library: `Langlands.Global.AdelicLeadingCuspidalComponents` (`StandardParabolicFamily`,
  `StandardIndex`, `top`, `HasExponent`, `constantTerm`, `positiveSplitComponent`,
  `IsAutomorphicOn`), `Langlands.Global.AdelicSquareIntegrableInducedForms`
  (`IsSquareIntegrableInducedForm`, Lapid's `A^2_P`), `compactHaarProbability`,
  `normOneRationalQuotientHaarMeasure`, and `IsIwasawaCompact.of_range_eq`
  (`Langlands.Global.AdelicEisensteinParabolicRangeTransport`).

## Definitions

Throughout, `𝓕 : StandardParabolicFamily F G` is a compatible family of standard parabolics
`P_J = M_J U_J` (for one maximal split torus, one generic cocharacter and one choice of
coroots), indexed by sets `J` of simple relative roots. `𝓕.top` is `G` itself.

### `StandardParabolicFamily.bot`

The index `J = ∅`. `𝓕.P 𝓕.bot` is the minimal standard parabolic `P_∅` of the family.

### `IsAutomorphicExponentDecomposition hsmooth Kinf rho J ψ s c`

`s` is a finite set of parameters `λ ∈ 𝔞_{P,ℂ}^* = ComplexCharacterParameter F P` (`P = P_J`)
and `c : 𝔞_{P,ℂ}^* → (G(𝔸) → ℂ)`, with

1. `ψ = ∑_{λ ∈ s} c λ`;
2. each `c λ`, `λ ∈ s`, is an automorphic function on `U(𝔸)M(F) \ G(𝔸)` (`IsAutomorphicOn`, for
   the archimedean compact subgroup `Kinf` and the embedding `rho`);
3. each `c λ`, `λ ∈ s`, has normalized exponent `λ` (`HasExponent`): there is `n` such that for
   every `g` the function `a ↦ δ_P(a)^{-1/2} (c λ)(a g) a^{-λ}` on `𝔄_P` (the positive real
   points of the split component, `positiveSplitComponent`) is a polynomial of degree at most
   `n` in `H_P(a)`.

Correspondence with (3.2). Delorme's term `e^{λ(H_P(g))} φ_{0,λ}(g)` with
`φ_{0,λ} ∈ S(𝔞_P^*) ⊗ A^n_P(G)` satisfies 3 (elements of `A^n_P` transform under `A_P^∞` by
`δ_P^{1/2} = a^{ρ_P}`), and it lies in `A_P(G)`, which gives 2. The exponents are distinct, being
the elements of a finite set. Unlike the Library's `IsExponentDecomposition`, the components are
not required to be cuspidal.

Existence. For an automorphic form `φ` on `G(F) \ G(𝔸)` the constant term `φ_P` is automorphic on
`U(𝔸)M(F) \ G(𝔸)`, and MW I.3.2 (with I.3.1) decomposes it by its exponents along `A_P`: group
the terms `a^λ Q(log a)` of MW's expansion by `λ`. This existence is not stated here; it is part
of the proof of `TemperedWeakConstantTermVanishingStatement` (see there).

Uniqueness. Two decompositions `(s, c)` and `(s', c')` of the same `ψ` have the same nonzero
components: for fixed `g`, `a ↦ ψ(a g)` on `𝔄_P` is then written in two ways as
`∑_λ a^{λ + ρ_P} Q_{g,λ}(H_P(a))`. The functions `X ↦ e^{μ(X)} X^k` on `𝔞_P` with distinct `μ`
are linearly independent, and `λ ↦ (a ↦ a^λ)` is injective on `𝔞_{P,ℂ}^*` because `H_P`
identifies `𝔄_P` with `𝔞_P = Hom(X^*(P), ℝ)`. So `c λ (a g) = c' λ (a g)` for all `a`, with
`c λ = 0` for `λ ∉ s` and `c' λ = 0` for `λ ∉ s'`; take `a = 1`.

### `unitaryExponentSum J s c`

`∑_{λ ∈ s, Re λ = 0} c λ`, with `Re λ = parameterRealPart F P λ ∈ X^*(P) ⊗ ℝ`. These are the
terms with unitary (normalized) exponents, `λ ∈ i𝔞_P^*`.

### `IsWeakConstantTerm hsmooth Kinf rho J φ ψ`

There is a decomposition `(s, c)` of the constant term `𝓕.constantTerm J φ`
(`∫_{U(F) \ U(𝔸)} φ(u g) du`) as above with `ψ = unitaryExponentSum J s c`. This is Delorme's
`ψ = φ_P^w` (Definition 3.7). By the uniqueness above, all decompositions give the same `ψ`, so
`IsWeakConstantTerm J φ` holds for at most one function `ψ`. Delorme defines `φ_P^w` for tempered
`φ`; the Lean predicate is meaningful for every `φ`.

The top index. For `J = 𝓕.top` the unipotent radical is trivial, the quotient `U(F) \ U(𝔸)` is a
point with the normalized measure, and `𝓕.constantTerm 𝓕.top φ = φ`. If `φ` transforms under a
unitary character `a ↦ a^{iν}` of `A_G` (and `ρ_G = 0` because `det Ad` is trivial on a
connected reductive group), then `φ` itself is a decomposition with the single exponent `iν`, and
`φ_G^w = φ`. Delorme uses this in the last step of the proof of Lemma 3.10 (ii).

### `squareIntegrablePairingIntegrand K J x φ ψ` and `squareIntegrablePairingMeasure K hKc J`

For `x ∈ P(𝔸)` the integrand is the function on `K × M(F) \ M(𝔸)^1`
(`NormOneRationalQuotient F M`)

`(k, m) ↦ φ(x m k) · conj ψ(x m k)`,

evaluated at the representative `m = Quotient.out` in `M(𝔸)^1`, with `x` and `m` mapped into
`G(𝔸)` by `p : P → G` and `l ≫ p : M → G`. The measure is the Haar probability measure of `K`
(`compactHaarProbability`) times the quotient of a Haar measure of `M(𝔸)^1` by `M(F)`
(`normOneRationalQuotientHaarMeasure`).

Correspondence with (3.7). For `x = exp_P X ∈ 𝔄_P` this is Delorme's integrand. Delorme writes
the domain as `M(𝔸)^1 × K`; the functions `φ ∈ A^2_P` and `ψ ∈ A^{temp}_P` are left
`M(F)`-invariant, and the integral is over `M(F) \ M(𝔸)^1 × K`, as the formula for `P = G` just
before (3.7) (an integral over `[G]^1`) shows. When `φ` and `ψ` are left
`M(F)`-invariant the integrand does not depend on the choice of representatives. The factor
`e^{-2ρ_P(X)}` of (3.7) is omitted: it is nonzero, so it does not affect the vanishing of the
integral or its convergence. A different normalization of the Haar measure of `M(𝔸)^1`
multiplies the integral by a positive constant.

### `IsSquareIntegrableOrthogonal K hKc rho hsmooth hcalc J ψ`

For every `φ` with `IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc (p J) (iU J) (l J) φ`
(Lapid's `A^2_P`, as in the published parent module) and every `x ∈ 𝔄_P`, the pairing integrand
is integrable and its integral vanishes.

Correspondence: `p_P(φ, ψ)(X) = (φ, ψ)^X_P` vanishes for all `X ∈ 𝔞_P` and all `φ ∈ A^2_P`, the
definition of `ψ ∈ 𝒜_P^{temp,c}(G)` (Delorme p.15), except that membership in `A_P^{temp}(G)` is
not required. Integrability is included so that no condition holds through the value `0` of a
divergent Bochner integral. It is no restriction for the weak constant terms used below:
by Lemma 3.8 (ii), `Φ_P^w ∈ A_P^{temp}(G)` for tempered `Φ`, and for `ψ ∈ A_P^{temp}(G)` Delorme
states that the integral (3.7) converges absolutely (p.15).

The condition is linear in `ψ`. Delorme's conclusion concerns the individual functions
`Φ_{P,0,μ}`, `μ ∈ E^w_P(Φ)`, and the weak constant term is
`Φ_P^w = ∑_μ e^{μ(H_P)} Φ_{P,0,μ}`. On the domain of the pairing at `x = exp_P X`,
`H_P(x m k) = X` (as `m ∈ M(𝔸)^1`, `k ∈ K`), so the factor `e^{μ(H_P)}` is the nonzero constant
`e^{μ(X)}` there. Hence `Φ_{P,0,μ} ∈ 𝒜_P^{temp,c}` for all `μ` gives the condition for `Φ_P^w`.
In the other direction, `Φ_P^w` is tempered (Lemma 3.8 (ii)), so for `ψ = Φ_P^w` the condition
is `Φ_P^w ∈ 𝒜_P^{temp,c}(G)`, the hypothesis of Lemma 3.10 (ii).

## Statements

`WavePacketWeakConstantTermOrthogonalityStatement` and `TemperedWeakConstantTermVanishingStatement`
carry the hypotheses of the target on `F`, `G`, `K`, `rho`, `hsmooth`, `hcalc`
(`IsConnectedReductive G`, `IsMaximalCompactSubgroup F G K`, `IsClosedSubgroup rho`), with the
minimal parabolic of the target replaced by a family `𝓕` and `hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K`
(`P_∅(𝔸) K = G(𝔸)`). The automorphic forms are those of the parent module:
`IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ` (automorphic on `G(F) \ G(𝔸)`,
a unitary `A_G`-character `a^{iν}`, and `Φ / σ_{[G]}^m ∈ L²([G])` for some `m`). Weak constant
terms are taken with `Kinf = K ∩ G(𝔸_∞)` (`K.comap (ofInfinite F G)`), the compact subgroup of
`IsAutomorphicFunctionOn` in `IsLogSquareIntegrableAutomorphicForm`.

### `MinimalParabolicStandardFamilyStatement`

For every connected reductive `G` over a number field `F` and every minimal parabolic
`p₀ : P₀ → G` (`IsMinimalParabolicSubgroup p₀`, `P₀` affine, `p₀` a closed immersion) there is a
family `𝓕` with `SubgroupFunctor.range (𝓕.p 𝓕.bot) = SubgroupFunctor.range p₀`.

Correspondence: Borel–Tits. A minimal parabolic contains a maximal split torus `T` and is the
parabolic of a generic cocharacter of `T`.

Proof (`minimalParabolicStandardFamily`, as implemented):

1. The published `AdelicSiegelFactors.siegelAlgebraicSetupExistence` gives a maximal split torus
   `i : T → G` and a generic cocharacter `ν` of `T` whose minimal standard parabolic
   `Standard.parabolicHom i ν ∅` is a minimal parabolic subgroup.
2. The published `GroupScheme.minimalParabolicConjugacy` gives a rational point `g` and an
   isomorphism `e : P_∅(T, ν) ≅ P₀` with `Standard.parabolicHom i ν ∅ ≫ Int(g) = e ≫ p₀`.
3. `i ≫ Int(g)` is a maximal split torus (`IsMaximalSplitTorus.comp_iso`) and `ν` is generic for
   it (`isGenericCocharacter_comp_ambientIso_iff`). Let
   `𝓕 = StandardParabolicFamily.ofMaximalSplitTorus` for `i ≫ Int(g)` and `ν`.
4. By compatibility, the range of `𝓕.p 𝓕.bot` is `standardParabolic (i ≫ Int(g)) ν ∅`, which is
   the preimage of `standardParabolic i ν ∅` under `Int(g)⁻¹`
   (`standardParabolic_comp_ambientIso`), that is the range of
   `Standard.parabolicHom i ν ∅ ≫ Int(g)` (`isRepresentedBy_parabolicHom`,
   `SubgroupFunctor.range_comp_iso`). By step 2 this is the range of `e ≫ p₀`, which is the range
   of `p₀` (`SubgroupFunctor.range_iso_comp`).

### `WavePacketWeakConstantTermOrthogonalityStatement` (Delorme §§4–7)

Let `Φ` satisfy `IsLogSquareIntegrableAutomorphicForm` and
`∫_{[G]} Φ(y.out) · conj Θ(y.out) dμG(y) = 0` for every `Θ` with `IsWavePacket` (the target's
hypothesis, with the target's measure `μG`). Then for every `J` and every `ψ` with
`𝓕.IsWeakConstantTerm … J Φ ψ`, `𝓕.IsSquareIntegrableOrthogonal K … J ψ`.

Correspondence: the part of the proof of Theorem 7.9 after Lemma 7.10, up to and excluding the
application of Lemma 3.10 (ii). By Proposition 3.5 (see the provenance of
`IsLogSquareIntegrableAutomorphicForm` in the parent module) `Φ` is tempered with a unitary
character `ν_G`. For `a = a_1 ⊗ a_2` the Fourier inversion formula on `i𝔞_G^*` gives
`∫_{[G]} E_a Φ̄ = a_2(ν_G) ∫_{[G]^1} E_{a_1} Φ̄`. Lemma 7.11, proved with Theorem 7.1 and
Proposition 7.8, writes `∫_{[G]^1} E_{a_1} Φ̄` through the polynomials
`p_P(φ, Φ_{P,0,μ})`, `μ ∈ E^w_P(Φ)`. The hypothesis makes these vanish for all `P`, `φ`, `a_1`,
`a_2`, and Delorme concludes `Φ_{P,0,μ} ∈ 𝒜_P^{temp,c}(G)`, hence the Lean conclusion for
`ψ = Φ_P^w` (see `IsSquareIntegrableOrthogonal`). The packets `E_a` used there are packets of
`IsWavePacket` for the standard parabolics `P_J`, built from the family (presentation, coordinates
`e` on `𝔞_P^*`, `a(λ) φ` as `∑_j c_j ⊗ v_j`), as in the parent module. Packets of other parabolics
are not used.

### `TemperedWeakConstantTermVanishingStatement` (Delorme §3)

Let `Φ` satisfy `IsLogSquareIntegrableAutomorphicForm`, and suppose that for every `J` and every
`ψ` with `𝓕.IsWeakConstantTerm … J Φ ψ`, `𝓕.IsSquareIntegrableOrthogonal K … J ψ`. Then
`Φ g = 0` for every `g ∈ G(𝔸)`.

Correspondence: Lemma 3.10 (ii). Its proof needs:

- Temperedness. `Φ` is tempered by Proposition 3.5. The Lean hypothesis bounds only `Φ` in the
  weighted `L²` norm; the derivatives `R_u Φ` follow by Harish-Chandra's `Φ = Φ * α`, as in the
  provenance of `IsLogSquareIntegrableAutomorphicForm` in the parent module.
- Existence of the weak constant terms. For each `J`, MW I.3.2 provides a decomposition of
  `𝓕.constantTerm J Φ` (Definitions), so the hypothesis applies to `ψ = Φ_{P_J}^w`, which is
  tempered by Lemma 3.8 (ii). With the correspondence of `IsSquareIntegrableOrthogonal`,
  `Φ_{P_J}^w ∈ 𝒜_{P_J}^{temp,c}(G)` for every standard `P_J`.
- Lemma 3.10 (ii) then gives `Φ = 0`. Its proof is an induction on `dim 𝔞_0^G`: the induction
  hypothesis on the Levi subgroups and Lemma 3.8 give `Φ_P^w = 0` for `P ≠ G`, Lemma 3.10 (i)
  then writes `Φ` as `e^{iν(H_G)} Φ_0` with `Φ_0 ∈ A^2(G)`, and `Φ = Φ_G^w ∈ 𝒜^{temp,c}(G)`
  (see "The top index") forces `Φ_0 = 0`. `Φ` is continuous, so `Φ = 0` as an automorphic form
  means `Φ g = 0` for every `g`.

### The compact subgroup

Delorme fixes `K` in good position with respect to the minimal Levi subgroup of `P_∅`. Here `K`
is any maximal compact subgroup with `P_∅(𝔸) K = G(𝔸)`, as in the target. This class is larger
than Delorme's, and the two statements are not reduced to the good-position case here. At the
archimedean places every such `K_v` is `π_v K'_v π_v⁻¹` with `K'_v` in good position and
`π_v ∈ P_∅(F_v)`, by the conjugacy of maximal compact subgroups and the Iwasawa decomposition for
`K'_v`. At a finite place this can fail: a maximal compact `K_v` with `P_∅(F_v) K_v = G(F_v)` need
not be the stabilizer of a special point. For `G = PGL₂` over `ℚ`, `P_∅` the upper triangular
Borel and a prime `p`, the full stabilizer of an edge of the tree (the normalizer of an Iwahori
subgroup) is maximal compact, is not conjugate to a vertex stabilizer, and still satisfies
`B(ℚ_p) K_p = PGL₂(ℚ_p)`. A proof of the two statements must therefore either treat such `K`
directly or supply a different reduction. What does hold (explanatory, not proved here) is the
transfer when `K = π K' π⁻¹` with `K'` in good position and `π ∈ P_∅(𝔸)`: right translation
`R(π⁻¹)`, `(R(π⁻¹)f)(g) = f(g π⁻¹)`, carries:

- automorphic forms, `K_∞`-finiteness to `K'_∞`-finiteness, the `A_G`-character and the weighted
  `L²` condition (`σ_{[G]}(y π) − σ_{[G]}(y)` is bounded and `μG` is right invariant), and
  weak constant terms (constant terms and exponents commute with right translation);
- `A^2_P` for `K` onto `A^2_P` for `K'`;
- the pairing: if `π = u m_π a_π` with `u ∈ U(𝔸)`, `m_π ∈ M(𝔸)^1`, `a_π ∈ 𝔄_P`, then the
  pairing for `K` at `x` equals the pairing for `K'` at `x a_π` of the translated functions (right
  invariance of the measure on `M(F) \ M(𝔸)^1`, and conjugation by `π` carries the Haar
  probability of `K'` to that of `K`); since the condition is required for all `x ∈ 𝔄_P`, it is
  preserved;
- wave packets: `H^K_P(g) = H^{K'}_P(g π) − H_P(π)`, so
  `E^K(v, λ)(g) = e^{-λ(H_P(π))} E^{K'}(R(π⁻¹) v, λ)(g π)`. A packet for `K'` of a standard
  parabolic is the `R(π⁻¹)`-translate of a packet for `K` with the coefficients `c_j` multiplied by
  the smooth function `x ↦ e^{i e(x)(H_P(π))}` of modulus `1`; the continuations change by an
  entire factor. So orthogonality of `Φ` to the packets for `K` gives orthogonality of
  `R(π⁻¹)Φ` to the standard packets for `K'`, which is all that Delorme uses.

### Integrals

The Bochner integrals in `IsSquareIntegrableOrthogonal` are paired with integrability, so the
condition never holds through the value `0` of a divergent integral. The orthogonality hypothesis
of `WavePacketWeakConstantTermOrthogonalityStatement` is the target's, whose integrands are
integrable by the parent module's discussion ("Integrals").

## The reduction theorem

`temperedWavePacketVanishing_of_reduction` takes `MinimalParabolicStandardFamilyStatement`,
`WavePacketWeakConstantTermOrthogonalityStatement` and
`TemperedWeakConstantTermVanishingStatement` and proves `TemperedWavePacketVanishingStatement`.

Proof (as implemented): introduce the data of the target, `Φ` and the orthogonality hypothesis.

1. Destructure the target's hypothesis into a minimal parabolic `p₀ : P₀ → G` with
   `IsIwasawaCompact p₀ K`.
2. `MinimalParabolicStandardFamilyStatement` gives `𝓕` with
   `range (𝓕.p 𝓕.bot) = range p₀`, and `IsIwasawaCompact.of_range_eq` gives
   `IsIwasawaCompact (𝓕.p 𝓕.bot) K`.
3. `WavePacketWeakConstantTermOrthogonalityStatement`, applied to `𝓕` and the orthogonality
   hypothesis, gives the hypothesis of `TemperedWeakConstantTermVanishingStatement`, which gives
   `Φ g = 0`.

`temperedWavePacketVanishing_of_weakConstantTerms` applies `temperedWavePacketVanishing_of_reduction`
to `minimalParabolicStandardFamily`, so `WavePacketWeakConstantTermOrthogonalityStatement` and
`TemperedWeakConstantTermVanishingStatement` alone imply the target. All theorems of the module use
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

`MinimalParabolicStandardFamilyStatement` is proved here. The other two statements are not.
Separate `lean.proof@1` tasks for them follow once this module is accepted. Their expected
inputs:

- `WavePacketWeakConstantTermOrthogonalityStatement`: Delorme §4–§7 (uniform temperedness of
  Eisenstein series, the truncated inner products of Theorem 7.1 and Proposition 7.8 with Arthur's
  truncation, Lemma 7.11, Fourier analysis on `A_G`), the Library's continuation, constant-term
  and holomorphy statements for Eisenstein series, and a treatment of the compact subgroups that
  are not `P_∅(𝔸)`-conjugate to one in good position (see "The compact subgroup");
- `TemperedWeakConstantTermVanishingStatement`: Delorme §3 (Propositions 3.5, 3.6, Lemmas 3.8,
  3.10), MW I.3–I.4 (exponents and square-integrability criteria), and the same treatment of the
  compact subgroups.
