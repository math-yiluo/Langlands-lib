# Unramified local factors of pairs

Author: Worker 11. This module is in namespace `Langlands.RankinSelberg`. It
states Cogdell's computation of the local factors of a pair of unramified
generic representations of `GL_n(F)` and `GL_m(F)`, and the Jacquet-Shalika
bounds on the parameters of a unitary generic unramified representation. Let
`A` and `A'` be the Langlands classes of the two representations, and let `q`
be the residue cardinality. There are four statements:

- in equal rank, the integral of the normalized spherical Whittaker vectors
  against the characteristic function of `O^n` is `det(1 - A ⊗ A' q^(-s))⁻¹`;
- in every rank, `L(s, π × σ) = det(1 - A ⊗ A' q^(-s))⁻¹`;
- in every rank, `ε(s, π × σ, ψ) ≡ 1`;
- the parameters `χ_i(ϖ)` satisfy `q^(-1/2) < |χ_i(ϖ)| < q^(1/2)`.

The module defines two auxiliary objects, four statements and their
conjunction. None of the statements is proved.

## Sources

**Cogdell, *Analytic theory of L-functions for GL_n*.** Chapter 9 of
J. Bernstein and S. Gelbart (eds.), *An Introduction to the Langlands
Program*, Birkhäuser Boston, 2004, pages 197-228. Registered as
`cogdell-2004-analytic-theory-gln`. The 1-based PDF page is the printed page
plus 3. The text layer is usable except in displays, which were read from
rendered pages.

- **§3.1, printed page 211.** `k` is a nonarchimedean local field with ring
  of integers `o`, prime ideal `p`, a generator `ϖ` of `p` and
  `q = |o/p| = |ϖ|⁻¹`. `ψ` is a nontrivial continuous additive character.
  "`(π, V_π)` and `(π', V_π')` will now be the smooth vectors in irreducible
  admissible unitary generic representations of `GL_n(k)` and `GL_m(k)`,
  respectively."
- **Printed pages 212-213.** The local integrals are `Ψ(s; W, W')` for
  `m < n` and `Ψ(s; W, W', Φ)` for `m = n`, with `W ∈ 𝒲(π, ψ)`,
  `W' ∈ 𝒲(π', ψ⁻¹)` and `Φ ∈ 𝒮(k^n)`. For `m < n` the ideals `I_j(π, π')`
  of the blocks `j` "are the same". `L(s, π × π') = P(q^(-s))⁻¹`, with
  `P(0) = 1`, "is the normalized generator of the fractional ideal
  `I(π, π')` formed by the family of local integrals" (Theorem 3.1).
- **Printed page 214.** Theorem 3.2 is the local functional equation, with
  the sign `ω'(-1)^(n-1)`. It is followed by the definition
  `ε(s, π × π', ψ) = γ(s, π × π', ψ) L(s, π × π') / L(1 - s, π̃ × π̃')`.
  Then: "The first case to consider is that where both `π` and `π'` are
  unramified. Since they are assumed generic, they are both full induced
  representations from unramified characters of the Borel subgroup."
- **Printed page 215.** `π ≃ Ind(μ_1 ⊗ ⋯ ⊗ μ_n)` and
  `π' ≃ Ind(μ'_1 ⊗ ⋯ ⊗ μ'_m)` with unramified `μ_i`, `μ'_j`, and the
  Satake classes are `A_π = diag(μ_1(ϖ), …, μ_n(ϖ))` and
  `A_π' = diag(μ'_1(ϖ), …, μ'_m(ϖ))`. "In the Whittaker models there will be
  unique normalized `K = GL(o)`-fixed Whittaker functions, `W_o ∈ 𝒲(π, ψ)`
  and `W'_o ∈ 𝒲(π', ψ⁻¹)`, normalized by `W_o(e) = W'_o(e) = 1`."
  **Theorem 3.3.** "If `π`, `π'`, and `ψ` are all unramified, then
  `L(s, π × π') = det(I - q^(-s) A_π ⊗ A_π')⁻¹`, which equals
  `Ψ(s; W_o, W'_o)` if `m < n` and `Ψ(s; W_o, W'_o, Φ_o)` if `m = n`,
  and `ε(s, π × π', ψ) ≡ 1`."

**Cogdell, *Lectures on L-functions, converse theorems, and functoriality
for GL_n*.** Fields Institute lectures, 2003, author-posted version.
Registered as `cogdell-2003-fields-lectures-www`. The 0-based PDF page index
is the printed page plus 3.

- **Lecture 6, printed page 45.** "For this lecture and the next `k` will be
  a non-archimedean local field", with `|ϖ|⁻¹ = |O/p| = q`. "Let `(π, V_π)`
  be an irreducible admissible smooth unitary generic representation of
  `GL_n(k)` and `(π', V_π')` a representation of `GL_m(k)` satisfying the
  same hypotheses."
- **Lecture 7, §1, printed pages 54-55.** An unramified generic `π` is
  `Ind(μ_1 ⊗ ⋯ ⊗ μ_n)` with unramified `μ_i`, and `A_π = diag(μ_i(ϖ))`. The
  normalized spherical vector of the induced model satisfies
  `f°(nak) = δ_(B_n)^(1/2)(a) ∏ μ_i(a_i)`.
- **§2, printed page 56.** "Take `ψ` … to also be unramified and
  non-trivial, so `ψ(O) = 1` but `ψ(ϖ⁻¹) ≠ 1`."
- **§3, printed page 57.** The integral is computed through the Iwasawa
  decomposition `h = n ϖ^J k`, `dh = dn δ_(B_m)⁻¹(ϖ^J) dk`.
- **Printed page 58.** Theorem 7.1: "If `π`, `π'`, and `ψ` are all
  unramified, then `L(s, π × π') = det(I - q^(-s) A_π ⊗ A_π')⁻¹ =
  Ψ(s, W°, W'°)`." Moreover `L(s, π) = det(I - q^(-s) A_π)⁻¹`. "The same
  result holds for `GL_n × GL_n`. One then takes for the Schwartz function
  `Φ ∈ 𝒮(k^n)` the characteristic function `Φ°` of `O^n ⊂ k^n`." Corollary
  7.1.1: "If `π`, `π'`, and `ψ` are all unramified, then
  `ε(s, π × π', ψ) ≡ 1`." Corollary 7.1.2: "Suppose that `π` is a[n]
  irreducible unitary generic unramified representation of `GL_n(k)`,
  `π ≃ Ind(μ_1 ⊗ ⋯ ⊗ μ_n)`. Then the Satake parameters `μ_i(ϖ)` satisfy
  `q^(-1/2) < |μ_i(ϖ)| < q^(1/2)`." The proof, on page 59, applies the
  `GL_n × GL_n` computation to `π` and its complex conjugate. It uses the
  absolute convergence of the local integral for `Re(s) ≥ 1`, "since `π` is
  unitary".

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data, and
`O = F.canonicalTopologicalData.Integers` is the integer ring of its
canonical valuation. Representations are actual representations of
`GL_m(F)` on complex vector spaces in universes `uV` and `uW`. `ψ` is a
`UnitaryAdditiveCharacter`, which is nontrivial by definition. The published
module `UnramifiedPairStatement` supplies three objects:

- `unramifiedClass F χ`, the tuple `i ↦ χ_i(ϖ)` for the canonical
  uniformizer `ϖ`;
- `unramifiedEulerFactor q a a' s = (∏_i ∏_j (1 - a_i a'_j q^(-s)))⁻¹`;
- `IsUnramifiedGenericConstituent F ψ π χ`: `π` is generic for `ψ`
  (irreducible, admissible, with a nonzero standard Whittaker functional),
  it has a nonzero `GL(O)`-fixed vector, the quasi-characters `χ_i` are
  unramified, and `π` is a subquotient of the normalized principal series
  `i(χ_1, …, χ_m)`.

This module defines two auxiliary objects. Both are objects of the sources.

- `integerLatticeIndicator F n` is `Φ°`, the characteristic function of
  `O^(n+1)` in the row space `F^(n+1)` (`Fin (n + 1) → F`). It is the
  published `Hecke.TestFunction.characteristic` of the product set
  `Set.univ.pi (fun _ => O)`, which makes it a `SchwartzBruhat` function.
  The set is clopen because `O` is open and closed for the valuation
  topology, and compact by `isCompact_integers` and Tychonoff.
- `unramifiedLPolynomial a a'` is the polynomial
  `∏_i ∏_j (1 - a_i a'_j X)`. For diagonal `A`, `A'` with eigenvalue tuples
  `a`, `a'`, the matrix `A ⊗ A'` is diagonal with entries `a_i a'_j`. So the
  polynomial at `X = q^(-s)` is `det(1 - A ⊗ A' q^(-s))`. Its constant
  coefficient is 1, the normalization `P(0) = 1` of the source's
  L-polynomial.

## Statements

`UnramifiedEqualRankIntegralStatement` (Theorem 3.3 for `m = n`; the
`GL_n × GL_n` sentence after Theorem 7.1). Take any `p`, `F`, `n`, and
representations `π`, `σ` of `GL_(n+1)(F)`. Take tuples `χ`, `χ'` of
quasi-characters with `IsUnramifiedGenericConstituent F ψ π χ` and
`IsUnramifiedGenericConstituent F ψ σ χ'`, and assume `π` and `σ` are
`IsUnitarizable`. Let `q`, `abv`, `ϖ` and `μ` satisfy the published
`IsJacquetNormalization q ψ abv ϖ μ`. That is: `q` is the residue
cardinality, `ϖ` is a uniformizing element, `abv` is the normalized absolute
value, `ψ` has conductor `O`, and `μ` is the quotient measure on
`N_(n+1) \ GL_(n+1)(F)` compatible with the Haar measures giving
`GL_(n+1)(O)` and `N_(n+1)(O)` mass one. Let `ℓ` be a nonzero `ψ`-Whittaker
functional on `π`, `ℓ'` a nonzero `ψ⁻¹`-Whittaker functional on `σ`, and
`w`, `w'` any elements of `SphericalTest π ℓ` and `SphericalTest σ ℓ'`.
These are right `GL_(n+1)(O)`-invariant vectors of the coefficient models
with value 1 at `e`. Then there is a real `c` such that, for every `s` with
`Re s > c`:

- `EqualRankConverges ψ abv μ w w' Φ° s` holds;
- `equalRankModelIntegral ψ abv μ π σ ℓ ℓ' w w' Φ° s` equals
  `unramifiedEulerFactor q (unramifiedClass F χ) (unramifiedClass F χ') s`.

Here `Φ° = integerLatticeIndicator F n`. The first item is absolute
convergence. The published integral is
`∫_(N \ GL_(n+1)) w(g) w'(g) Φ°(e_(n+1) g) |det g|^s dμ(g)`.

`UnramifiedPairLFactorStatement` (Theorem 3.3; Theorem 7.1). Take any `p`,
`F`, `r`, `n`, representations `π` of `GL_(r+1)(F)` and `σ` of
`GL_(n+1)(F)` in either rank order, and tuples `χ`, `χ'`. Let `ψ` satisfy
`HasIntegerConductor ψ` (`ψ` trivial on `O` and on no larger fractional
ideal), and let `ν` be any additive Haar measure on `F`. Assume
`IsUnramifiedGenericConstituent F ψ π χ`,
`IsUnramifiedGenericConstituent F ψ σ χ'`, and that `π` and `σ` are
`IsUnitarizable`. Then `IsPadicSymmetricLPolynomial F ψ ν π σ P` holds for
`P = unramifiedLPolynomial (unramifiedClass F χ) (unramifiedClass F χ')`.
This says `L(s, π × σ) = P(q^(-s))⁻¹ = det(1 - A ⊗ A' q^(-s))⁻¹`.

`UnramifiedPairEpsilonStatement` (Theorem 3.3; Corollary 7.1.1). Same
hypotheses, except that `ν : SelfDualHaar F.canonicalTopologicalData ψ` is
a Haar measure self-dual for `ψ`. Then
`IsPadicSymmetricEpsilonFactor F ψ ν.val π σ (1, 0)` holds. A value
`(c, m)` of the published relation means `ε(s) = c q^(-ms)`, so `(1, 0)`
means `ε(s, π × σ, ψ) ≡ 1`.

`UnramifiedUnitaryParameterBoundStatement` (Corollary 7.1.2). Take any `p`,
`F`, `r`, a representation `π` of `GL_(r+1)(F)`, a tuple `χ` and an
additive character `ψ`. Assume `IsUnramifiedGenericConstituent F ψ π χ` and
that `π` is `IsUnitarizable`. Then for every `i`,
`q^(-1/2) < ‖χ_i(ϖ)‖ < q^(1/2)`. Here `q` is
`F.canonicalTopologicalData.residueCardinality`, the powers are real powers,
and `χ_i(ϖ)` is `unramifiedClass F χ i`.

`UnramifiedFactorStatement` is the conjunction of the four statements.

## Interpretation

- **Unitarity.** Both sources work under a standing hypothesis of
  irreducible admissible unitary generic representations: Analytic theory
  §3.1, and Lecture 6 of the Fields lectures. So the first three statements
  assume `IsUnitarizable π` and `IsUnitarizable σ`. `IsUnitarizable` is the
  existence of an invariant positive definite Hermitian form. For
  irreducible admissible representations this is unitarity in the sources'
  sense. The original computation, in Jacquet-Shalika, *On Euler products
  and the classification of automorphic forms I* (Amer. J. Math. 103
  (1981)), is now registered in the project literature as
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`.
  The statements here retain the unitary scope of the two sources cited above;
  the version without unitarity is not stated here.
- **Unramified `ψ`.** The Fields lectures define "unramified" by
  `ψ(O) = 1` and `ψ(ϖ⁻¹) ≠ 1`. This implies that `O` is the conductor of
  `ψ`, which is `HasIntegerConductor ψ`. Conversely, if `ψ` has conductor
  `O`, then `ψ(ϖ⁻¹u) ≠ 1` for some unit `u`, so `ψ(ϖ'⁻¹) ≠ 1` for the
  uniformizer `ϖ' = ϖu⁻¹`. The classes `μ_i(ϖ)` of unramified characters do
  not depend on the uniformizer. So the hypothesis is read as conductor `O`,
  the wording of Jacquet-Shalika, *Euler products II*, §1.3. In the integral
  statement it is part of `IsJacquetNormalization`.
- **Unramified representations and their classes.** "`π` unramified" is
  the existence of a nonzero `GL(O)`-fixed vector. The class
  `A_π = diag(μ_i(ϖ))` is attached through `π ≃ Ind(μ_1 ⊗ ⋯ ⊗ μ_n)`. The
  predicate `IsUnramifiedGenericConstituent` asks instead that `π` be a
  subquotient of `i(χ)`. As explained in `UnramifiedPairStatement`, this
  determines `χ` up to order, and the conclusions do not depend on the
  order. The induction is normalized in both: Fields §1 writes
  `f°(nak) = δ^(1/2)(a) ∏ μ_i(a_i)`, and the published `principalSeries` is
  normalized.
- **Whittaker vectors.** The sources' `W_o ∈ 𝒲(π, ψ)` and
  `W'_o ∈ 𝒲(π', ψ⁻¹)` are the unique `GL(o)`-fixed vectors with value 1 at
  `e`. The integral statement quantifies over every nonzero functional and
  every normalized spherical vector of its coefficient model. The Whittaker
  functional is unique up to scalars, so every such model is the source's
  model. The normalized spherical vector of such a model is unique
  (Jacquet-Shalika, *Euler products II*, §1.3, stated as the published
  `UnramifiedSphericalVectorStatement`). So the quantified statement is
  the source's statement about `W_o` and `W'_o`.
- **Measures in the integral.** The Fields computation uses
  `dh = dn δ⁻¹(ϖ^J) dk`. This is the Iwasawa form of the quotient measure of
  the Haar measures giving `K` and `N(O)` volume one, as in
  Jacquet-Shalika, *Euler products II*, §1.4. This is the `measure` field of
  `IsJacquetNormalization`. For `GL_1 × GL_1` the statement is Tate's
  computation: with `O^×` of volume one,
  `∫_(F^×) χ χ'(x) 1_O(x) |x|^s d^×x = Σ_(j ≥ 0) (χ(ϖ) χ'(ϖ) q^(-s))^j
  = (1 - χ(ϖ) χ'(ϖ) q^(-s))⁻¹`.
- **Convergence.** The sources state the identity for the integral and
  note that it converges for `Re s` large (absolutely for `Re s ≥ 1` in the
  unitary case, Analytic theory p.212). The statement asserts absolute
  convergence and the identity on some half plane `Re s > c`, with `c`
  unspecified.
- **The L-factor for every `ν`.** The published relation asks that `P` be
  the normalized generator of the ideal of every block `j` in unequal rank,
  and of the equal-rank ideal in equal rank. The source defines `L` as the
  generator of `I(π, π')` after noting that all the `I_j(π, π')` coincide
  (p.213). The relation also quantifies over every compatible quotient
  measure. The additive Haar measure `ν` enters only through the measures on
  the rectangular variables of the blocks `j ≥ 1`. Rescaling `ν` or the
  quotient measure multiplies each integral by a positive constant, which
  does not change an ideal. So the L-factor of the source does not depend on
  `ν`, and the statement holds for every `ν`.
- **The ε-factor and `ν`.** The sources' `ε` is the factor of
  Jacquet-Piatetski-Shapiro-Shalika, defined with the Haar measure self-dual
  for `ψ`. The published relation defines that factor only for self-dual
  `ν`, so the statement takes `ν : SelfDualHaar`. The sign
  `ω'(-1)^(n-1)` of the functional equation (Theorem 3.2; Fields Theorem
  6.2) enters the published relation as a power of the scalar `ζ` with
  `W'(-g) = ζ W'(g)` on the model of the smaller-rank member. For an
  unramified member `ζ = ω'(-1) = 1`, because `-1` is a unit and the
  `χ'_j` are trivial on units.
- **Rank order.** Cogdell treats `π` on `GL_n` and `π'` on `GL_m` with
  `m ≤ n`. The published symmetric relations read the pair with the larger
  rank first, as in JPSS (2.12). If `r < n`, the conclusion is therefore
  the relation for `(σ, π)`, which is Theorem 3.3 for that pair. Its
  polynomial `∏_j ∏_i (1 - a'_j a_i X)` has the same factors as
  `unramifiedLPolynomial a a'`.
- **The unequal-rank integral.** For `m < n` Theorem 3.3 also states
  `L(s, π × π') = Ψ(s; W_o, W'_o)`. The identity
  `Ψ(s; W_o, W'_o) = det(1 - A ⊗ A' q^(-s))⁻¹` is the published
  `UnramifiedPairIntegralStatement` (Jacquet-Shalika, *Euler products II*,
  §1.4 (3); Fields Proposition 7.5). It is not repeated here.
- **Special cases.** For `σ` the trivial character of `GL_1(F)` (`n = 0`,
  `χ' = 1`), which is unitary, generic and unramified with class `(1)`, the
  L- and ε-statements give `L(s, π) = det(1 - A q^(-s))⁻¹` and
  `ε(s, π, ψ) = 1` (Fields, p.58).
- **Genericity in the bounds.** The bounds need genericity. The trivial
  representation of `GL_2(F)` is unitary and unramified, but its class is
  `diag(q^(1/2), q^(-1/2))`. The bound is strict, as in Corollary 7.1.2.
  `ψ` in the bound statement is any character for which `π` is generic.
- **Field.** `F` is a p-adic field because the spherical subgroup, the
  principal series and the canonical topological data are published only for
  `PadicField`. Cogdell allows any nonarchimedean local field (in Lecture 7,
  of characteristic 0).
- **Not stated.** Not stated here:
  - the computations without unitarity;
  - the Hecke-algebra results and Shintani's formula, Fields Propositions
    7.1-7.4;
  - the remark that the conductor of an unramified `π` is 0.

## Universes

`integerLatticeIndicator` has the universe parameter `uF` (the field), and
`unramifiedLPolynomial` has none. `UnramifiedUnitaryParameterBoundStatement`
has `uF` and `uV` (the space of `π`). `UnramifiedEqualRankIntegralStatement`,
`UnramifiedPairLFactorStatement`, `UnramifiedPairEpsilonStatement` and
`UnramifiedFactorStatement` have `uF`, `uV` and `uW` (the space of `σ`).
