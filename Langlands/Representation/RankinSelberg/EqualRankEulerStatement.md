# Equal-rank integrals of Jacquet and Shalika, Euler products I

Author: Worker 11. This module is in namespace `Langlands.RankinSelberg`. It
states three results of Jacquet-Shalika on the equal-rank integrals
`Ψ(s, W, W', Φ)` of two generic representations of `GL_r(F)`:

- for unitary generic `π` and `σ`, the integrals converge absolutely in
  `Re s ≥ 1` (Proposition (1.5)(i));
- for unitary generic `π` and `σ`, every nonzero `W` and every `s` with
  `Re s ≥ 1`, some `W'` and `Φ` give a nonzero integral (Proposition
  (1.5)(ii));
- for generic unramified `π` and `σ`, unitary or not, the integral of the
  normalized spherical vectors against the characteristic function of
  `O^r` is `det(1 - A ⊗ A' q^(-s))⁻¹` for `Re s` large (Proposition (2.3)).

The module defines no new objects: three statements and their conjunction.
None of the statements is proved.

## Source

**Jacquet-Shalika, *On Euler products and the classification of automorphic
representations I*.** Amer. J. Math. 103 (1981), 499-558. Registered as
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`.
The 0-based PDF page index is the printed page minus 499. The text layer is
usable except for bars and displays, which were read from rendered pages.
`G_r = GL_r(F)` for a nonarchimedean local field `F`, `K = GL_r(O)`, `N` the
upper triangular unipotent subgroup and `𝒲(π; ψ)` the `ψ`-Whittaker model.

- **(1.5), printed page 507.** "Suppose now that `π` and `π'` are
  irreducible *unitary* generic representations of `G_r`. For
  `Φ ∈ 𝒮(F^r)`, `W ∈ 𝒲(π; ψ)`, and `W' ∈ 𝒲(π'; ψ)`, we set
  `Ψ(s, W', W, Φ) = ∫_(N\G) W'(g) W̄(g) Φ(εg) |det g|^s dg` (1) where `ε`
  is the following row vector: `ε = (0, 0, …, 1)`." **Proposition.** "(i)
  The integral (1) converges absolutely in the half space `Re(s) ≥ 1`,
  normally for `Re(s)` in a compact subset of `[1, ∞[`. (ii) Given `W' ≠ 0`
  and `s` with `Re(s) ≥ 1`, there exist `W` and `Φ` such that
  `Ψ(s, W', W, Φ) ≠ 0`."
- **Printed pages 507-510.** The proofs. The proof of (ii) ends with
  "for appropriate normalizations of the measures" and
  `Ψ(s, W', W, Φ) = ∫_K F(k) F̄(k) dk`, which is nonzero.
- **(1.6) Remark, printed page 510.** "One can show" that the integrals have
  a g.c.d. `L(s, π × π') = P(q^(-s))⁻¹`. This is not proved in the paper.
- **(2.1), printed pages 510-511.** An unramified `π` is "the unique
  unramified component of an induced representation of the form
  `Ind(G_r, B_r; μ_1, μ_2, …, μ_r)` where the `μ_i`'s are unramified
  quasi-characters". The class is `A = diag(μ_1(ϖ), …, μ_r(ϖ))`, and
  `L(s, π × π') = det(1 - q^(-s) A ⊗ A')⁻¹` (2). "(The definition is
  consistent with the one given in (1.6), as we will prove in a subsequent
  paper.)" "If `π` corresponds to `A` then the imaginary conjugate `π̄`
  corresponds to `Ā`."
- **(2.2), printed page 511.** "Now suppose `π` is generic. Suppose also
  that the largest ideal of `F` on which `ψ` is trivial is `O`. Then the
  space `𝒲(π; ψ)` contains a unique element `W` invariant under `K`.
  Moreover `W(e) ≠ 0` and we may normalize `W` by requiring that
  `W(e) = 1`." This is the essential element. Its values are
  `W(ϖ^J) = δ^(1/2)(ϖ^J) Tr(ρ_J(A))` for dominant `J` (2).
- **(2.3) Proposition, printed pages 511-512.** "Let `π` and `π'` be
  admissible irreducible representations of `G_r`. Suppose they are generic
  and unramified. Let `W` and `W'` be the essential elements of `𝒲(π; ψ)`
  and `𝒲(π'; ψ)` respectively. Suppose `Φ` is the characteristic function
  of `𝔑`. Then, as meromorphic functions in `Re(s) > 1`,
  `Ψ(s, W', W, Φ) = L(s, π × π̄')`, the measures being normalized by the
  conditions `vol(N ∩ K) = 1`, `vol(K) = 1`." Here `𝔑` is the lattice
  `O^r`. The proof (p.512) supposes `Re(s)` large, where the integral
  converges, writes it as
  `Σ_(J ∈ T_+(r)) Tr ρ_J(A') conj(Tr ρ_J(A)) X^(tr J)` with `X = q^(-s)`,
  and then, "after replacing `A` by `Ā`", proves
  `Σ_J Tr ρ_J(A') Tr ρ_J(A) X^(tr J) = det(1 - A ⊗ A' X)⁻¹` (3).

## Statements

Throughout, `F : PadicField p` carries its canonical topological data, and
representations are actual representations of `GL_(n+1)(F)` on complex
vector spaces in universes `uV` and `uW`. `ψ` is a
`UnitaryAdditiveCharacter`, which is nontrivial by definition. The
integral is the published
`equalRankModelIntegral ψ abv μ π σ ℓ ℓ' W W' Φ s
= ∫_(N \ GL_(n+1)) W(g) W'(g) Φ(e_(n+1) g) |det g|^s dμ(g)`, a Bochner
integral, for `W` in the coefficient model of a `ψ`-Whittaker functional
`ℓ` on `π` and `W'` in the coefficient model of a `ψ⁻¹`-Whittaker
functional `ℓ'` on `σ`. Absolute convergence is the published
`EqualRankConverges`.

`UnitaryEqualRankConvergenceStatement` (Proposition (1.5)(i)). Take any
`p`, `F`, `n` and `ψ`. Bind the instance
`Measure.IsMulRightInvariant (unipotentHaar F n)`, as the published
analytic statements do. Take any quotient measure `μ` on `N_(n+1) \
GL_(n+1)(F)` satisfying `IsCompatible` for the published
`generalLinearHaar F n` and `unipotentHaar F n` (the Haar measures giving
`GL_(n+1)(O)` and `N_(n+1)(O)` mass one). Let `π` and `σ` satisfy
`Whittaker.IsGeneric ψ n` (irreducible, admissible, with a nonzero standard
`ψ`-Whittaker functional) and `IsUnitarizable`. Let `ℓ` be a nonzero
`ψ`-Whittaker functional on `π` and `ℓ'` a nonzero `ψ⁻¹`-Whittaker
functional on `σ`. Then for all `W`, `W'` in the two coefficient models,
every `Φ : SchwartzBruhat (Fin (n + 1) → F)` and every `s` with
`1 ≤ Re s`, `EqualRankConverges ψ |·| μ W W' Φ s` holds. Here `|·|` is
the published `normalizedAbsoluteValue`.

`UnitaryEqualRankNonvanishingStatement` (Proposition (1.5)(ii)). The same
hypotheses. For every nonzero `W` in the coefficient model of `ℓ` and every
`s` with `1 ≤ Re s`, there are `W'` in the coefficient model of `ℓ'` and a
Schwartz-Bruhat `Φ` with `equalRankModelIntegral ψ |·| μ π σ ℓ ℓ' W W' Φ s
≠ 0`.

`UnramifiedGenericEqualRankIntegralStatement` (Proposition (2.3)). Take
any `p`, `F`, `n`, representations `π`, `σ` of `GL_(n+1)(F)` and tuples
`χ`, `χ'` of quasi-characters with `IsUnramifiedGenericConstituent F ψ π χ`
and `IsUnramifiedGenericConstituent F ψ σ χ'` (published in
`UnramifiedPairStatement`: generic for `ψ`, a nonzero `GL(O)`-fixed vector,
unramified `χ_i`, and a subquotient of the normalized principal series
`i(χ)`). No unitarity is assumed. Let `q`, `abv`, `ϖ` and `μ` satisfy the
published `IsJacquetNormalization q ψ abv ϖ μ`: `q` is the residue
cardinality, `ϖ` a uniformizing element, `abv` the normalized absolute
value, `ψ` of conductor `O`, and `μ` the quotient measure compatible with
the Haar measures giving `GL_(n+1)(O)` and `N_(n+1)(O)` mass one. Let `ℓ`,
`ℓ'` be nonzero functionals as above, and `w`, `w'` any elements of
`SphericalTest π ℓ` and `SphericalTest σ ℓ'` (right
`GL_(n+1)(O)`-invariant vectors of the coefficient models with value 1 at
`e`). Then there is a real `c` such that for every `s` with `Re s > c` the
integral of `w`, `w'` against `Φ° = integerLatticeIndicator F n` converges
absolutely and equals
`unramifiedEulerFactor q (unramifiedClass F χ) (unramifiedClass F χ') s
= ∏_(i,j) (1 - χ_i(ϖ) χ'_j(ϖ) q^(-s))⁻¹`.

`EqualRankEulerStatement` is the conjunction of the three statements.

## Interpretation

- **From `W' W̄` to `W W'`.** Jacquet-Shalika take both functions in
  `ψ`-models and integrate `W' W̄`. The JPSS form used in the Library takes
  `W ∈ 𝒲(π; ψ)`, `W' ∈ 𝒲(σ; ψ⁻¹)` and integrates `W W'`. The two agree
  through the complex conjugate representation `σ̄`, which acts by the same
  operators on the conjugate space. If `ℓ'` is a `ψ⁻¹`-Whittaker
  functional on `σ`, then `v ↦ conj(ℓ'(v))` is a `ψ`-Whittaker functional
  on `σ̄`, and the model `𝒲(σ̄; ψ)` is `{W̄' : W' ∈ 𝒲(σ; ψ⁻¹)}`. The
  representation `σ̄` is irreducible, admissible, unitary or unramified
  exactly when `σ` is. Apply the source with its `(π, π')` equal to
  `(σ̄, π)` and its `(W, W')` equal to `(W̄', W)`. Then the source's
  integrand `W W̄̄' = W W'` is the Library integrand, with `ε g` the last
  row `e_(n+1) g`.
- **Genericity.** The statements assume that `σ` is generic for `ψ` and
  has a nonzero `ψ⁻¹`-Whittaker functional `ℓ'`. The source needs `σ̄`
  generic for `ψ`, which is the existence of `ℓ'`. A representation is
  generic for `ψ` exactly when it is generic for `ψ⁻¹` (conjugation by
  `diag((-1)^i)`), so the nonzero `ℓ'` exists for every generic `σ`. The
  statements take it as a hypothesis and use no such implication.
- **Unitarity.** `IsUnitarizable` is the existence of an invariant positive
  definite Hermitian form. For irreducible admissible representations this
  is unitarity in the source's sense.
- **Measures in (1.5).** The source integrates over `N \ G` with
  unspecified Haar measures ("for appropriate normalizations of the
  measures" in the proof of (ii)). The statements quantify over every
  quotient measure compatible with the published normalized Haar measures.
  Another choice of Haar measures multiplies the quotient measure by a
  positive constant, which changes neither absolute convergence nor
  nonvanishing. Existence of a compatible measure is the separate published
  `QuotientHaarExistenceStatement`.
- **Uniformity.** The clause "normally for `Re(s)` in a compact subset of
  `[1, ∞[`" of (1.5)(i) is not stated.
- **Bochner integral in (1.5)(ii).** `equalRankModelIntegral` is a Bochner
  integral, which is 0 for a non-integrable integrand. At `Re s ≥ 1` the
  integrand is integrable by (1.5)(i), so the nonvanishing statement is the
  source's.
- **The value in (2.3).** The source's computation gives
  `Ψ(s, W', W, Φ) = Σ_J Tr ρ_J(A') Tr ρ_J(Ā) X^(tr J)
  = det(1 - Ā ⊗ A' X)⁻¹`, by (3) for `Ā` in place of `A`. By (2.1) this is
  `L(s, π̄ × π')`, where `π` carries the conjugated function. The printed
  value `L(s, π × π̄')` is `det(1 - A ⊗ Ā' X)⁻¹`, which differs in general:
  for `r = 1`, `π = χ` and `π' = χ'`, Tate's computation gives
  `∫ χ'(x) χ̄(x) 1_O(x) |x|^s d^×x = (1 - χ̄(ϖ) χ'(ϖ) q^(-s))⁻¹`. The
  statement uses the computed value. Under the dictionary above, the
  source's `π` is `σ̄`, of class `Ā'`, and its `π'` is `π`, of class `A`.
  So the value is `det(1 - A' ⊗ A X)⁻¹ = det(1 - A ⊗ A' X)⁻¹`, the
  published `unramifiedEulerFactor`. This agrees with Cogdell's form of the
  computation (Analytic theory, Theorem 3.3), stated in the published
  `UnramifiedFactorStatement`.
- **Essential elements.** The source's essential element of `𝒲(σ̄; ψ)` is
  `W̄'_0`, for `W'_0` the normalized spherical vector of `𝒲(σ; ψ⁻¹)`. The
  statement quantifies over every nonzero functional and every normalized
  spherical vector. The normalized spherical vector of a model is unique
  (Jacquet-Shalika, *Euler products II*, §1.3, the published
  `UnramifiedSphericalVectorStatement`), and so is the Whittaker functional
  up to scalars. So the quantified statement is the source's statement
  about the essential elements.
- **Unramified representations and classes.** As in
  `UnramifiedPairStatement`, "unramified component of `Ind(μ)`" is read as
  `IsUnramifiedGenericConstituent`: a subquotient of the normalized
  principal series `i(χ)` with a nonzero `GL(O)`-fixed vector. The induction
  is normalized, as the formula `W(ϖ^J) = δ^(1/2)(ϖ^J) Tr ρ_J(A)` of (2.2)
  requires. "The largest ideal of `F` on which `ψ` is trivial is `O`" is
  `HasIntegerConductor ψ`, part of `IsJacquetNormalization`, as are the
  measure conditions `vol(K) = vol(N ∩ K) = 1`.
- **Half plane in (2.3).** The source states the identity "as meromorphic
  functions in `Re(s) > 1`", and its proof works for `Re(s)` large, where
  the integral converges. The statement asserts absolute convergence and
  the identity on some half plane `Re s > c`, with `c` unspecified. It does
  not assert meromorphic continuation; rationality is the published
  `EqualRankAnalyticStatement`.
- **Relation to published statements.** Without unitarity,
  `UnramifiedGenericEqualRankIntegralStatement` implies the published
  `UnramifiedEqualRankIntegralStatement`, which adds `IsUnitarizable`
  hypotheses. The source does not identify its g.c.d. with the factor (2)
  ("as we will prove in a subsequent paper"), so the published unramified
  L- and ε-statements keep their unitary scope.
- **Field.** `F` is a p-adic field because the spherical subgroup, the
  principal series and the canonical topological data are published only for
  `PadicField`.
- **Not stated.** The uniformity in (1.5)(i), Remark (1.6), the explicit
  formula (2.2)(2) and the results of the later sections.

## Universes

All four declarations have the universe parameters `uF` (the field), `uV`
(the space of `π`) and `uW` (the space of `σ`).
