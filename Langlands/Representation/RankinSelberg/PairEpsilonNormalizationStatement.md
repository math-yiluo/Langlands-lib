# Normalizations of epsilon factors of pairs

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
two normalizations of the Rankin-Selberg epsilon factors of pairs of
Jacquet, Piatetski-Shapiro and Shalika:

- the central value `ε(1/2, π × π̌, ψ) = ω_π(-1)^(n-1)`, from Bushnell and
  Henniart, *Calculs de facteurs epsilon de paires pour GL_n sur un corps
  local, I*, Bull. London Math. Soc. 31 (1999), 534-542, Théorème 2;
- the form of the exponent, `f(π₁ × π₂, ψ) = n₁ n₂ c(ψ) + f(π₁ × π₂)` with
  `f(π₁ × π₂)` independent of `ψ`, from Bushnell, Henniart and Kutzko, *Local
  Rankin-Selberg convolutions for GL_n: explicit conductor formula*,
  J. Amer. Math. Soc. 11 (1998), 703-730, introduction.

The epsilon factors are the relations `IsPadicPairEpsilonFactor` (module
`LocalConverseStatement`) and `IsPadicSymmetricEpsilonFactor` (module
`PadicPairFactors`). The module defines three statements. None of them is
proved.

## Source

- **Bushnell-Henniart 1999** (registered as
  `bushnell-henniart-1999-epsilon-pairs`; read from the text layer, printed
  page = 0-based PDF index + 534).
  - **Abstract and §1.1, printed page 534.** `F` is a non-Archimedean local
    field, `ψ` a nontrivial additive character, and `n(ψ)` the largest
    integer `k` such that `ψ` is trivial on `p_F^(-k)`. For every irreducible
    admissible representation `π` of `GL_n(F)` with central quasicharacter
    `ω_π`, Théorème 2 gives `ε(π × π̌, ψ, 1/2) = ω_π(-1)^(n-1)`. The epsilon
    factor is that of [10], which is JPSS 1983.
  - **§1.3, printed page 535.** For supercuspidal `π` of `GL_n(F)` and `π'`
    of `GL_(n')(F)`, the exponent `a(π × π')` is defined by
    `ε(π × π', ψ, s + t) = ε(π × π', ψ, s) q^(-t(a(π × π') + n n' n(ψ)))`
    for `s, t ∈ ℂ`. "Ces exposants sont des entiers ne dépendant pas de
    `ψ`."
  - **§3.1, Théorème 2, printed page 538.** "Soit `π ∈ A_F(n)`. On a
    `ε(π × π̌, ψ, 1/2) = ω_π(-1)^(n-1)`." Here `A_F(n)` is the set of classes
    of irreducible admissible representations of `GL_n(F)` (§1.2, printed
    page 535). In the proof, `π` is the Langlands quotient of a parabolic
    induction from `π₁ ⊗ ⋯ ⊗ π_r`, and
    `ε(π × π̌, ψ, s) = ∏_(i,j) ε(π_i × π̌_j, ψ, s)`. This holds by JPSS §9.4
    and Theorem 3.1 if `π` is generic, "ou par définition dans le cas
    général".
  - **§3.3, printed page 540.** For generic `π`, the functional equation is
    that of JPSS Theorem 2.7. It uses Whittaker functions `W ∈ W(π; ψ)` and
    `W' ∈ W(π̌; ψ̄)`, the map `W ↦ (g ↦ W(w ᵗg⁻¹))`, and the Fourier
    transform on `Fⁿ` for the measure self-dual for `(x, y) ↦ ψ(tr(ᵗy x))`.
    The equation is
    `Ψ(1 - s, W̃, W̃'; Φ̂) / L(π̌ × π, 1 - s) = ω_π̌(-1)^(n-1) ε(π × π̌, ψ, s) Ψ(s, W, W'; Φ) / L(π × π̌, s)`.
- **Bushnell-Henniart-Kutzko 1998** (registered as
  `bhk-1998-explicit-conductor`; read from the text layer, printed page =
  0-based PDF index + 703).
  - **Introduction, printed page 703.** `c(ψ)` is the largest integer `c`
    such that `p^(-c) ⊂ Ker ψ`. For irreducible smooth representations `π_i`
    of `GL_(n_i)(F)`, `i = 1, 2`, JPSS attach `L(π₁ × π₂, s)` and
    `ε(π₁ × π₂, s, ψ)`. Then
    `ε(π₁ × π₂, s, ψ) = ε(π₁ × π₂, 0, ψ) q^(-f(π₁ × π₂, ψ) s)` for an integer
    `f(π₁ × π₂, ψ)`. "In fact, `f(π₁ × π₂, ψ) = n₁n₂c(ψ) + f(π₁ × π₂)`,
    where `f(π₁ × π₂)` is independent of `ψ`."
  - **§5.1, Comments, printed page 718.** The same identity for the pair
    `(π̌₁, π₂)`, `π_i` irreducible generic unitary:
    `f(π̌₁ × π₂, ψ) = f(π̌₁ × π₂) + n₁n₂c(ψ)`, `f(π̌₁ × π₂)` independent of
    `ψ`.
- **JPSS 1983**, *Rankin-Selberg convolutions* (registered as
  `jpss-1983-rankin-selberg`), §2.1, printed page 386 / PDF page 21,
  formula (4) and the following paragraph: the Whittaker function
  transformation and, separately for irreducible representations, the
  Gelfand-Kazhdan identification with the contragredient. The original scan
  was read visually for the status distinction below.
- **Henniart 2002**, *Une caractérisation de la correspondance de Langlands
  locale pour GL(n)* (registered as `henniart-2002-characterization`), §2.8,
  printed page 596 / PDF page 10: Langlands quotients of essentially
  square-integrable data and the product formula for epsilon factors of
  arbitrary irreducible pairs. This supplies the convention of the separate
  `LanglandsFactors` interface discussed below.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data, `q` is
its residue cardinality `F.canonicalTopologicalData.residueCardinality`, `ψ`
is a `UnitaryAdditiveCharacter` of `F` (continuous and nontrivial), and `ν` is
in the published `LocalFactor.PadicAbelian.SelfDualHaar
F.canonicalTopologicalData ψ`. The relation `IsPadicPairEpsilonFactor F ψ ν π σ
e`, `e = (c, m) : ℂˣ × ℤ`, says `ε(s, π × σ, ψ) = c q^(-ms)`:

- a compatible quotient measure exists;
- `π` has a nonzero standard Whittaker functional for `ψ` and `σ` one for
  `ψ⁻¹`;
- for every compatible quotient measure and every pair of nonzero
  functionals, the JPSS functional equation holds with this monomial.

`IsPadicSymmetricEpsilonFactor` is the same relation with the larger rank
read first.

- `ContragredientEpsilonCentralValueStatement` (Théorème 2, generic case)
  quantifies over:
  - every `p`, `F`, `ψ` and `ν` as above, and every `r`;
  - every representation `π` of `GL_(r+1)(F)` on a complex vector space in
    universe `uV` with `Whittaker.IsGeneric ψ r π`;
  - every `ω : Fˣ →* ℂˣ` with
    `Classification.HasGLCentralCharacter F (r + 1) π ω`, that is, the scalar
    matrix `a · 1` acts by `ω(a)`.

  It concludes that there is `e : ℂˣ × ℤ` with
  `IsPadicPairEpsilonFactor F ψ ν.val π (smoothContragredient π) e` and
  `e.1 · q^(-e.2 / 2) = ω(-1)^r`. The power is the complex power of the
  positive real `q`. `Whittaker.IsGeneric ψ r π` is irreducibility,
  admissibility and a nonzero standard Whittaker functional for `ψ`.
  `smoothContragredient π` is the published smooth contragredient, the
  action on the smooth vectors of the dual.
- `PairEpsilonExponentStatement` quantifies over:
  - every `p`, `F` and all `r`, `t`;
  - representations `π` of `GL_(r+1)(F)` (universe `uV`) and `σ` of
    `GL_(t+1)(F)` (universe `uW`) that are irreducible
    (`Representation.IsIrreducible`) and admissible (`Langlands.IsAdmissible`,
    which includes smoothness).

  It concludes that there is an integer `a` with the following property. For
  every `ψ`, every `ν` self-dual for `ψ` and every `e` with
  `IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e`,
  `e.2 = a + (r + 1)(t + 1) · F.canonicalTopologicalData.additiveConductor ψ`.
- `PairEpsilonNormalizationStatement` is the conjunction of the two
  statements.

## Interpretation

- **Central value.** With `e = (c, m)`, `ε(s, π × π̌, ψ) = c q^(-ms)` takes
  the value `c q^(-m/2)` at `s = 1/2`. The rank is `n = r + 1`, so
  `ω_π(-1)^(n-1)` is `ω(-1)^r`. Since `ω(-1)² = 1`, `ω(-1) = ±1`, and
  `ω_π̌(-1) = ω_π(-1)` in the sign of the functional equation.
- **Matching the functional equation.** The published relation is JPSS
  Theorem 2.7(iii) in equal rank. Its roles match BH99 §3.3:
  - `π` uses functionals for `ψ` and `π̌` functionals for `ψ⁻¹`;
  - the Fourier transform is the row transform `IsRowFourierPair` for the
    pairing `∑ x_i y_i` and the product measure of `ν` on the coordinates;
    this is the measure self-dual for `ψ(tr(ᵗy x))`;
  - the sign is `ζ^(n-1)`, where `ζ` is the scalar by which `-1` acts on
    the Whittaker model of the second member (`HasModelMinusOneScalar`). For
    the second member `π̌` this is `ω_π̌(-1)^(n-1)`.
- **Existence.** The statement asserts the existence of the epsilon factor
  of `(π, π̌)`, not only its value. This existence is JPSS Theorem 2.7 for
  the pair. It needs `π̌` to have a nonzero Whittaker functional for `ψ⁻¹`.
  Classically this follows from the Gelfand-Kazhdan theorem `π̌ ≅ π^ι`,
  `π^ι(g) = π(ᵗg⁻¹)`: for `W` a Whittaker function of `π` for `ψ`, the
  function `g ↦ W(w ᵗg⁻¹)` is one of `π^ι` for the conjugate character.
  BH99 §3.3 uses this map. The Library constructs `dualFunctional` in
  `Whittaker/DualTransform`, proves its formula (`dualFunctional_apply`)
  and preservation of nonvanishing (`dualFunctional_nonzero`), and proves
  the coefficient transformation (`dualFunction_coefficient`).
  `dualFunction_mem_whittakerSet` in `RankinSelberg/LocalFactor` proves that
  the transformed function belongs to the Whittaker set of
  `inverseTransposePullback π` for `ψ.scale (-1)`. These results do not
  identify that pullback with `smoothContragredient π`; the separate
  Gelfand-Kazhdan identification is still needed for this route to
  contragredient genericity. They also do not prove epsilon-factor existence
  or the central-value formula. Epsilon factors of a pair are unique
  (`IsPadicPairEpsilonFactor.unique`), so given existence the statement
  determines `ε(1/2, π × π̌, ψ)`.
- **Generic representations only.** BH99 states Théorème 2 for every
  irreducible admissible `π`. For nongeneric `π` the factor is defined as
  the product over the Langlands data (BH99 p.538; Henniart 2002 §2.8).
  This module's central-value goal uses the generic integral relation
  `IsPadicPairEpsilonFactor`. The separate `RankinSelberg/LanglandsFactors`
  module defines `IsLanglandsPairEpsilonFactor` using actual
  square-integrable Langlands quotient data for both representations and
  agreement with the block product for every such presentation. The
  existence clauses prevent vacuity from missing presentations.
  `IsLanglandsPairEpsilonFactor.unique` proves uniqueness, and
  `langlandsPairEpsilonFactor` constructs a factor from quotient-data
  witnesses, block-factor existence and presentation independence.
  `langlandsPairEpsilonFactorOfClassification` in
  `RankinSelberg/LanglandsFactorDescent` derives the independence step and
  constructs the factor from irreducibility,
  square-integrable exhaustion and classification hypotheses at the
  required carrier universes, and block-factor existence. Those inputs are
  not proved by the constructor. These conditional constructions do not
  establish unconditional nongeneric factor existence, comparison with the
  generic integral relation, or a nongeneric version of either normalization
  goal here. `Correspondence/FullFactorCompatibility` and
  `Correspondence/FullSpecification` consume the Langlands relation in
  their predicates and goals; neither module proves the correspondence.
- **Independence of `ψ`.** The value `ω_π(-1)^(n-1)` does not depend on `ψ`,
  and the statement holds for every `ψ` and `ν`. For `GL_1` it gives
  `ε(1/2, χ × χ⁻¹, ψ) = 1`, Tate's `ε(1/2, 1, ψ) = 1` for the self-dual
  measure.
- **Exponent.** In BHK's notation `ε(s) = ε(0) q^(-fs)`, so `m = f(π × σ, ψ)`
  and `c = ε(0)`. BHK's `c(ψ)` and BH99's `n(ψ)` are the largest `k` with `ψ`
  trivial on `p^(-k)`. This is the published `additiveConductor ψ`, the
  largest `k` with `ψ` trivial on `π^(-k) O`. The integer `a` is BHK's
  `f(π × σ)`. Placing `∃ a` before `∀ ψ ν e` expresses that it does not
  depend on `ψ` (nor on `ν`).
- **Scope of the exponent statement.** BHK state it for all irreducible
  smooth pairs. The published relation requires nonzero Whittaker
  functionals (for `ψ` on the member read first, for `ψ⁻¹` on the other).
  For a pair without them no `e` satisfies the relation, and the statement
  holds with any `a`. So its content concerns generic pairs, the pairs for
  which this module uses the integral-based epsilon relation. The separate
  Langlands-data relation above does not occur in this goal. Admissibility is a
  hypothesis. Every irreducible smooth representation of `GL_n(F)` is
  admissible (Jacquet, Bernstein), but the Library does not prove this.
  BH99 §1.3 gives the same exponent for supercuspidal pairs.
- **Rank order.** `IsPadicSymmetricEpsilonFactor` reads the pair with the
  larger rank first, as in JPSS (2.12). The factor `(r + 1)(t + 1)` is
  symmetric, so the statement covers both orders.
- **Measures and field.** `ν` self-dual for `ψ` is a hypothesis, as in the
  other JPSS units. `F` is a p-adic field because the canonical topological
  data and the p-adic relations are published only for `PadicField`. BH99
  and BHK allow any non-Archimedean local field.
- **Not stated.**
  - BHK's explicit formula for `f(π₁ × π₂)` (Theorem 6.5).
  - The Galois side (BH99 Théorème 1) and the comparison (2a).
  - The transformation of `ε` under `ψ ↦ ψ_a`, `ψ_a(x) = ψ(ax)`:
    `ε(s, π × π', ψ_a) = ω_π(a)^(n') ω_(π')(a)^n |a|^(n n'(s - 1/2)) ε(s, π × π', ψ)`.
    BH99 §3.4 (printed page 540) uses a reduction of this kind to assume
    `n(ψ) = 0`, but no original statement of it was found in the project
    literature.

## Universes

`ContragredientEpsilonCentralValueStatement` has universe parameters `uF`
(the field) and `uV` (the space of `π`). `PairEpsilonExponentStatement` and
`PairEpsilonNormalizationStatement` have `uF`, `uV` and `uW` (the space of
`σ`).

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.PairEpsilonNormalizationStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
