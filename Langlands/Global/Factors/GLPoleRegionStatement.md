# Pole regions of JPSS pair L-polynomials

This module states the `GL_n` half, part (ii), of Henniart (1986),
Proposition 4.5. Take a pair of generic irreducible representations `π`, `σ`
of `GL_n(F)` and `GL_m(F)` over a p-adic field `F`. Suppose either both are
essentially tempered, or one of them is supercuspidal. Then the JPSS
L-polynomial of `π × σ` and the reflected JPSS L-polynomial of the dual pair
have no common zero.

Henniart's Lemma 4.4 uses this hypothesis to recover L- and epsilon-factors
from an equality of gamma factors. The published
`Langlands.Global.GammaPolynomialSeparationStatement`, in
`Langlands/Global/Factors/SeparationStatement`, is that algebraic step. Its
no-common-zero hypotheses have exactly the form concluded here. The Weil-group
half, part (i), is the separate module
`Langlands/Global/Factors/WeilPoleRegionStatement`.

Everything is stated over actual representations of the actual groups
`GL_n(F)`, with the published JPSS zeta-value sets and L-polynomial relations.
The module introduces no substitute types and assumes no local-factor theorem.

## Actual objects

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p` and a realization
`T : F.TopologicalData`. The statements install `T`'s topology, valuation
and local-field structure, and Borel σ-algebras, exactly as Worker 11's
published `Langlands.RankinSelberg.EqualRankAnalyticStatement` and
`UnequalRankAnalyticStatement` do. The objects used are:

- Representations `π : Representation ℂ (GL_(n+1)(F)) V` and `σ` on carriers
  `V : Type uV`, `W : Type uW`. Positive ranks are written `n + 1`, so rank one
  is included.
- `Langlands.Whittaker.IsGeneric ψ n π`. This means `π` is irreducible, is
  admissible (smooth, with finite-dimensional fixed vectors for every open
  subgroup), and has a nonzero Whittaker functional for the standard character
  of `ψ` on the upper unipotent subgroup.
- `T.IsEssentiallyTempered π`, from `Classification/Tempered`. It says
  `ν^(-s) π` is tempered for some real `s`, where `ν = |det|` is
  residue-normalized. Tempered means admissible with a unitary central
  character, and all matrix coefficients in `L^(2+ε)` modulo the center for
  every `ε > 0` and every Haar measure. This is Kudla's definition, recorded in
  that module.
- `Langlands.GeneralLinear.IsSupercuspidal σ`, from
  `Classification/Supercuspidal`. It means admissible, with vanishing actual
  Jacquet module for every proper block parabolic and each of its conjugates.
- The published JPSS relations of Worker 31's
  `Langlands/Representation/RankinSelberg/LocalFactor`:
  - `IsEqualRankLPolynomial q ψ abv μ π σ P` and
    `IsUnequalRankLPolynomial q ψ abv j k μ ν π σ P`. Each says that `P(0) = 1`
    and that `1 / P` generates the Laurent-polynomial span of the zeta values
    of the pair. The zeta values are the rational continuations of the actual
    convergent JPSS integrals over all Whittaker functions of `π` (for `ψ`)
    and of `σ` (for `ψ⁻¹`). Thus `L(s, π × σ) = P(q^(-s))⁻¹`.
  - `dualEqualRankZetaValues` and `dualUnequalRankZetaValues`: the same zeta
    values for the pair `(π^ι, σ^ι)`. Here `π^ι(g) = π(ᵗg⁻¹)` is the published
    `inverseTransposePullback`, and the character is `ψ⁻¹ = ψ.scale (-1)`.
    This is the pair on the left side of the JPSS functional equation, and
    the unequal-rank block indices `j, k` are kept.
- The measure data of the published JPSS statements:
  - an arbitrary nontrivial unitary additive character `ψ`;
  - the right-invariance instance of `unipotentHaar`;
  - any quotient measure `μ` on `N \ GL_(n+1)` satisfying the published
    compatibility predicate `IsCompatible` with `generalLinearHaar` and
    `unipotentHaar`;
  - in unequal rank, any additive Haar measure `ν` on `F`, through
    `rectangularMeasure ν j (n + 1)`;
  - `q = T.residueCardinality` and `abv = normalizedAbsoluteValue T`, so that
    `|ϖ| = q⁻¹`.

## Helper definition

`Langlands.Global.GLPoleRegion.HasNoReflectedCommonZero q P Pdual` says that no
nonzero `z` satisfies both `P(z) = 0` and `Pdual(q⁻¹ z⁻¹) = 0`. Take `P` to be
the L-polynomial of `π × σ` and `Pdual` the L-polynomial of the dual pair. Then
this says that `P_{π×σ}` and Henniart's `P̃_{π×σ}(X) = P_{(π×σ)^∨}(q⁻¹X⁻¹)` of
§4.4 have no common zero. Zero is excluded because `P̃` is a polynomial in
`X⁻¹`, and in any case `P(0) = 1`. The predicate is the hypothesis of
`GammaPolynomialSeparationStatement` verbatim. With
`q = F.canonicalTopologicalData.residueCardinality` it unfolds to the predicate
`WeilPoleRegion.HasNoReflectedCommonZero F` of the Weil-side module. Here `q`
is an explicit argument, because the GL statements quantify every realization
`T`.

## The statements

`Langlands.Global.EqualRankPoleRegionStatement F T n` quantifies the following:

- a character `ψ`;
- the invariance instance;
- a compatible `μ`;
- carriers `V`, `W`;
- representations `π`, `σ` of `GL_(n+1)(F)`, with `π` generic for `ψ` and `σ`
  generic for `ψ⁻¹`.

It assumes that `π` and `σ` are both essentially tempered, or that `σ` is
supercuspidal. Then, for all polynomials `P`, `Pdual`, if `P` is the JPSS
L-polynomial of `(π, σ)` and `Pdual` is the normalized generator of the
dual-pair values, it concludes `HasNoReflectedCommonZero q P Pdual`.

`Langlands.Global.UnequalRankPoleRegionStatement F T n j k` is the same with
the following changes:

- `π` is a representation of `GL_(n+(j+k+1)+1)(F)`, the larger group, and `σ`
  of `GL_(n+1)(F)`.
- An additive Haar measure `ν` is also quantified.
- The relations are the block-`j` unequal-rank relation and the block-`j`
  dual-pair values.
- The hypothesis is that both are essentially tempered, or that `σ` is
  supercuspidal, or that `π` is supercuspidal.

`Langlands.Global.GLPairPoleRegionStatement` quantifies a prime `p`, a p-adic
field `F` and a realization `T`. It asserts the equal-rank statement for every
`n`, and the unequal-rank statement for every `n`, `j` and `k`. This covers
every pair of positive ranks, with the larger rank `n + (j + k + 1) + 1` and
every JPSS block `0 ≤ j ≤ r - t - 1`. The universe levels `uF` (the field),
`uV` (the carrier of `π`) and `uW` (the carrier of `σ`) are independent.

## Why the statement holds

This is a guide for the later proof. It follows Henniart's §4.8, and uses the
facts he records in §2.6 from Jacquet's and JPSS's work.

For generic irreducible representations the integral L-factor is Henniart's
`L(π × π')` of §2.5. For irreducible `π`, JPSS note on p.386 that `π^ι` is the
contragredient `π^∨`; this is recorded in `RankinSelberg/LocalFactor.md`, and
it is the Gelfand–Kazhdan theorem. So the dual values define `L(π^∨ × σ^∨)`.

Henniart begins §4.8 by writing both members through §2.6(a) as Langlands sums
of essentially square-integrable `Sp_(n_i)(ρ_i)` and `Sp_(m_j)(τ_j)`, with
supercuspidal `ρ_i`, `τ_j`. He deduces from §2.6 that `P_{π×π'}(X)` is a
product of linear factors `1 - χ(ϖ) q^(…) X`. Here `χ` runs over the unramified
characters relating `ρ_i` to a twist of `τ_j^∨`, and the dual polynomial has
the analogous form.

**Essentially tempered case.** Write `π = ν^a π_0` and `σ = ν^b σ_0` with
`π_0`, `σ_0` tempered. Then `L(s, π × σ) = L(s + a + b, π_0 × σ_0)`. By
§2.6(a), tempered means that all `Sp_(n_i)(ρ_i)` are square integrable. By
§2.6(b)(4), `|Sp_r(ρ)| = α^((r-1)/2)|ρ|`. With the product formula, this puts
every pole of `L(s, π_0 × σ_0)` in `Re s ≤ 0`. Hence every zero `z = q^(-s)`
of `P_{π×σ}` has `|z| ≥ q^(a+b)`.

The dual pair is `ν^(-a) π_0^∨`, `ν^(-b) σ_0^∨`, with `π_0^∨` and `σ_0^∨`
tempered. So every zero `w` of `P_{π^∨×σ^∨}` has `|w| ≥ q^(-a-b)`. A
reflected zero `z = q⁻¹ w⁻¹` then has `|z| ≤ q^(a+b-1)`. Since `q > 1`, the
two sets of zeros are disjoint. Henniart argues equivalently with the
normalized moduli `|χ(ϖ)| q^(…)`, which are independent of `i`, `j` and `χ`.

**Supercuspidal case.** Let `π'` be the supercuspidal member and `π` the other
member. By Zelevinsky's Theorem 9.7(b), a generic irreducible `π` is the
irreducible product `⟨Δ_1⟩^t × ⋯ × ⟨Δ_r⟩^t` of essentially square-integrable
`⟨Δ_i⟩^t`, no two of whose segments are linked. Juxtaposed segments are linked
(Zelevinsky §4.1: linked with disjoint supports). So no two components are
juxtaposed. This is Henniart's remark "for example `π` can be any generic
element".

Henniart's proof then concludes by "the same reasoning as in 4.7". With
`π' = τ` supercuspidal, the factors of `P_{π×π'}` come from
`L(α^(n_i-1) ρ_i × τ)`. By §2.6(b)(3), `Sp_r(ρ)^∨ = α^(1-r) Sp_r(ρ^∨)`, so the
factors of `P_{π^∨×π'^∨}` come from `L(ρ_i^∨ × τ^∨)`. A common zero forces
`ρ_j ≅ α^(n_i) ρ_i` for some `i`, `j`. For `i ≠ j`, that makes the components
juxtaposed in the sense of §2.6(c), which is excluded. For `i = j` it is
impossible by central characters.

When the supercuspidal member is the first JPSS member, the symmetry of
§2.6(e)(7), `L(π × π') = L(π' × π)`, reduces it to this case. The same holds
for the dual pair.

## Provenance and specializations

The source result is Henniart (1986), Proposition 4.5(ii), printed p.160:

> Assume that `π` and `π'` are essentially tempered or that `π'` is cuspidal
> and `π = ⊞ π_i` where the `π_i`'s are essentially square integrable and no
> two of them are juxtaposed (for example `π` can be any generic element of
> `𝒜_F`). Then `P_{π×π'}` and `P̃_{π×π'}` have no common zero.

Its proof is in §4.8, printed pp.162-163. Here `π, π' ∈ 𝒜_F` are irreducible
admissible (§2.5). Cuspidal means supercuspidal, `𝒜^0` in §2.5. The
formalization makes the following documented choices.

- **Generic domain.** The Library's JPSS L-polynomial is defined by the
  zeta integrals of Whittaker functions. It therefore attaches a factor only
  to representations with a nonzero Whittaker functional. For other
  representations the zeta values are `{0}` and no generator exists. The
  Langlands-data L-factor of non-generic representations (Henniart §2.6(a)(1))
  is not in the Library. Hence both members are assumed generic irreducible
  admissible.
  - In the tempered case this loses nothing, since irreducible essentially
    tempered representations are generic. That is a theorem, not used here.
  - In the supercuspidal case, Henniart's hypothesis on `π` is replaced by its
    instance that he names himself: `π` generic. Within the generic domain the
    two agree by Zelevinsky's Theorem 9.7, as explained above.
- **Characters.** `π` is generic for `ψ` and `σ` for `ψ⁻¹`. These are the
  characters of JPSS's Whittaker spaces `𝒲(π; ψ)` and `𝒲(π'; ψ̄)`.
  Henniart's L-factors do not involve `ψ`. Independence of genericity from the
  nontrivial character is a theorem, not used here.
- **Dual pair.** The formalization uses `(π^ι, σ^ι)` with `ψ⁻¹`, as in the
  JPSS functional equation, rather than the contragredients `(π^∨, π'^∨)` of
  Henniart §4.4. The identification `π^ι ≅ π^∨` for irreducible `π` is the
  Gelfand–Kazhdan theorem, not used here. The conclusion is then the
  hypothesis that `GammaPolynomialSeparationStatement` needs for the gamma
  factor of the JPSS functional equation (Worker 11's
  `Langlands/Representation/RankinSelberg/FunctionalEquationStatement`).
- **Supercuspidality.** Henniart §2.5 defines supercuspidal representations
  by compact support of coefficients modulo the center. The Library's
  predicate is vanishing of every proper Jacquet module. Together with
  irreducibility and admissibility, these agree by Jacquet's theorem, which is
  not used here.
- **Rank order.** JPSS's unequal-rank integrals put the representation of
  larger rank first. Henniart's `π'` may have either rank, and his factors are
  symmetric (§2.6(e)(7)). So the unequal-rank statement allows either member
  to be supercuspidal. The equal-rank statement keeps Henniart's order, with
  `σ = π'` supercuspidal.
- **Blocks and measures.** The statement holds for every block `j` and uses
  the same block for the dual pair. JPSS assert that the factor does not
  depend on `j`. That independence is not needed, and not assumed.
  - Every compatible `μ` and every additive Haar `ν` are allowed. The
    published `isEqualRankLPolynomial_smul_measure` and its unequal analogue
    show that positive rescaling of the measure does not change the L-polynomial.
  - The existence of a compatible `μ` is the separate published proposition
    `QuotientHaarExistenceStatement`.
  - The existence of the L-polynomials is JPSS Theorem 2.7, Worker 11's
    `Theorem27Statement`.
  - Neither existence is assumed. The conclusion is stated for every `P` and
    `Pdual` satisfying the relations.
- **p-adic fields.** Henniart allows any nonarchimedean local field. The
  Library's JPSS objects are stated over `PadicField`, that is, finite
  extensions of `ℚ_p`. That case is stated, for every realization `T`.

## Original sources

Guy Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*,
Annals of Mathematics (2) 123 (1986), 145-203. Registered source:
`henniart-1986-cyclic`. Printed page `p` is PDF page `p - 143`.

- §2.5, printed pp.151-152 (PDF pp.8-9):
  - `𝒜(A)`, `𝒜^0(A)` and contragredients;
  - `L(τ × ρ) = P_{τ×ρ}(q^(-s))⁻¹` with `P_{τ×ρ}(0) = 1`, from [JPS 2];
  - the gamma factor `ε L(τ^∨ × ρ^∨)(1-s) / L(τ × ρ)(s)`.
- §2.6 (a)-(e), printed pp.152-153 (PDF pp.9-10):
  - Langlands sums `⊞`;
  - `Sp_r(ρ)` and (3)-(6);
  - linked and juxtaposed;
  - genericity, citing Zelevinsky Theorem 9.7;
  - the symmetry (7).
- §4.4, printed p.159 (PDF p.16): `P̃_τ(X) = P_{τ^∨}(q⁻¹X⁻¹)` and the
  separation lemma.
- §4.5 Proposition (ii), printed p.160 (PDF p.17).
- §4.8, printed pp.162-163 (PDF pp.19-20): proof of (ii).

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
Ann. Sci. ÉNS 13 (1980), 165-210. Registered source:
`zelevinsky-1980-induced-ii`.

- §4.1, printed p.184 (PDF p.21): linked and juxtaposed segments, as quoted in
  the published `Classification/Segments` module.
- Theorem 9.7, printed p.199 (PDF p.36), read directly: every non-degenerate
  irreducible representation is `⟨Δ_1⟩^t × ⋯ × ⟨Δ_r⟩^t` with no two segments
  linked.

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), 367-464. Registered source:
`jpss-1983-rankin-selberg`, SHA-256 `d9feed63…62245`. This scan has no text
layer. The conventions used here are those of the published modules that
implement its §2.1 and Theorem 2.7: `π^ι`, `𝒲(π; ψ)`, `𝒲(π'; ψ̄)`, the zeta
integrals and the normalized generator. Their authors read the scan; see
`RankinSelberg/LocalFactor.md`, `AnalyticStatement.md` and
`FunctionalEquationStatement.md`.

## Dependencies and acceptance boundary

The module imports the following published modules, all from Library commit
`354dfade`:

- `Langlands.Representation.RankinSelberg.LocalFactor`;
- `Langlands.Representation.RankinSelberg.AnalyticStatement`;
- `Langlands.Representation.Classification.Tempered`;
- `Langlands.Representation.Classification.Supercuspidal`.

The closing declaration `Langlands.Global.GLPairPoleRegionStatement` is a
proposition definition. Lean checking reports level parameters
`uF uV uW` and only the standard axioms. No theorem is proved here. No axioms,
instances, or hypotheses equivalent to the conclusion are introduced.
