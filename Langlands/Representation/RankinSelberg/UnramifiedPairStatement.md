# The unramified computation of Rankin-Selberg integrals

Author: Worker 11. This module is in namespace `Langlands.RankinSelberg`. It
states the unramified computation of Jacquet and Shalika, *On Euler products
and the classification of automorphic forms II*, Amer. J. Math. 103 (1981),
777-815, §1.3-§1.5, which has three parts. The Whittaker model of an
unramified generic representation has a unique normalized spherical vector.
For two such representations of different ranks, the Rankin-Selberg integral
of these vectors is `det(1 - A ⊗ A' q^(-s))⁻¹`. For unitary representations
this Euler factor has no pole in `Re s ≥ 1`. The module defines two auxiliary
functions, one auxiliary predicate and four statements. None of the
statements is proved.

## Source

Registered as `jacquet-shalika-1981-euler-products-ii`. The PDF is a scan,
read visually; 1-based PDF page = printed page - 775.

- **§0.3, printed page 779.** "Notations are the same as in part I", that is,
  *On Euler products and the classification of automorphic forms I* (Amer. J.
  Math. 103 (1981), 499-558). Part I is not in the project literature. The
  symbols used below are read with their standard meanings: `O` the ring of
  integers (a Fraktur letter in the scan), `ϖ̃` a uniformizer, `q` the residue
  cardinality, `G_r = GL(r, F)`, `K = GL(r, O)`, `B_r` the upper Borel
  subgroup, `N_r` the upper unipotent group, and `θ(n) = ψ(Σ n_(i,i+1))`.
- **§1.1, printed pages 779-780.** "In this section, `F` is a
  non-archimedean local field." An irreducible admissible `π` is generic if
  there is a linear form `λ ≠ 0` with `λ(π(n)v) = θ(n)λ(v)` for `n ∈ N_r(F)`.
  "The form `λ` is then unique up to a scalar factor", and the space
  `𝒲(π; ψ)` of the functions `W(g) = λ(π(g)v)` depends only on `ψ` and `π`.
- **§1.3, printed page 780.** "Suppose that `π` is unramified, that is it
  contains the trivial representation of `K`. Suppose further that the largest
  ideal on which `ψ` is trivial is `O`. Then up to scalars there exists exactly
  one element `W_0` in `𝒲(π; ψ)` invariant under `K` on the right. Moreover
  `W_0(e) ≠ 0` and we normalize `W_0` by requiring `W_0(e) = 1` ([C-S],
  [T.S.])." `W_0` is called the *essential element* of `𝒲(π; ψ)`. If `π` is
  unramified, then `π` is "the unique unramified component of an induced
  representation of the form `Ind(G_r, B_r; μ_1, μ_2, …, μ_r)`, where the
  `μ_i` are unramified quasi-characters". The class attached to `π` is by
  definition the class of `A = diag(μ_1(ϖ̃), μ_2(ϖ̃), …, μ_r(ϖ̃))`.
- **§1.4, printed pages 780-781.** Let `r > r'`. For `W ∈ 𝒲(π; ψ)` and
  `W' ∈ 𝒲(π'; ψ)`, display (1) defines
  `Ψ(s, W, W') = ∫_(N_(r') \ G_(r')) W(diag(g, 1)) W'(εg) |det g|^(s-(r-r')/2) dg`,
  with `ε = diag(1, -1, 1, -1, …)` (2) and `dg` an invariant measure. "It
  follows from the majorization of `W` and `W'` by gauges that the integral
  converges for `Re(s)` large." Then: "suppose that `π` and `π'` are
  unramified, the largest ideal on which `ψ` is trivial is `O`, and that the
  measure `dg` is the quotient of the Haar measures of `G_(r')` and `N_(r')`
  normalized so that `K` and `K ∩ N_(r')` have volume one. Then if `W` and `W'`
  are the essential elements of `𝒲(π; ψ)` and `𝒲(π'; ψ)` respectively, one
  has `Ψ(s, W, W') = det(1 - A ⊗ A' q^(-s))⁻¹` (3), where `A` (resp. `A'`) is
  the conjugacy class associated to `π` (resp. `π'`)." The proof writes `Ψ` as
  a sum over dominant `J` (4) and applies the explicit formulae (2.1) and
  Proposition (2.4) of part I (5). "We will denote the Euler factor in (3) by
  `L(s, π × π')`."
- **Proposition (1.5), printed page 782.** "(i) With the above notations,
  given `W'` there is a `W` such that the integral (1.4.1) converges and is
  equal to one for all `s`. (ii) Assume `π` and `π'` are unitary. Then the
  integral (1.4.1) converges for `Re(s) ≥ 1`, normally for `Re(s)` in a
  compact set. (iii) If `π` and `π'` are unitary and unramified then
  `L(s, π × π')` does not have a pole in `Re(s) ≥ 1`." Proof of (iii): "The
  third assertion follows from the second one."

The references [C-S] and [T.S.] are Casselman-Shalika, *The unramified
principal series of p-adic groups II* (1980), and Shintani, *On an explicit
formula for class-1 "Whittaker functions" on GL_n over p-adic fields* (1976).
Both are in the central library. They are not cited here as sources of the
statements.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data, and `ϖ`
in `unramifiedClass` is its canonical uniformizer
`F.canonicalTopologicalData.uniformizerUnit`. Representations are actual
representations of `GL_m(F)` on complex vector spaces in universes `uV` and
`uW`. `ψ` is a `UnitaryAdditiveCharacter`, which is nontrivial by definition.
Quasi-characters are the published `QuasiCharacter F`, continuous
homomorphisms `Fˣ → ℂˣ`.

- `unramifiedClass F χ` is the tuple `i ↦ χ_i(ϖ)` for `χ : Fin m →
  QuasiCharacter F`. It lists the eigenvalues of the class
  `A = diag(χ_1(ϖ), …, χ_m(ϖ))` of §1.3.
- `unramifiedEulerFactor q a a' s` is
  `(∏_i ∏_j (1 - a_i a'_j q^(-s)))⁻¹`. For diagonal `A`, `A'` with eigenvalue
  tuples `a`, `a'`, `A ⊗ A'` is diagonal with entries `a_i a'_j`. So this is
  `det(1 - A ⊗ A' q^(-s))⁻¹`.
- `IsUnramifiedGenericConstituent F ψ π χ`, for `π` of `GL_(r+1)(F)` and
  `χ : Fin (r+1) → QuasiCharacter F`, is a conjunction of four conditions:
  - `π` is generic for `ψ` (`Whittaker.IsGeneric ψ r π`: irreducible,
    admissible, with a nonzero standard Whittaker functional).
  - The `GL_(r+1)(O)`-fixed vectors of `π` (`fixedVectors π (sphericalSubgroup
    F r)`) are nonzero.
  - Every `χ_i` is unramified (`IsUnramifiedCharacter`: trivial on the
    valuation units).
  - `π` is a subquotient of the published normalized principal series
    `principalSeries F r χ = i(χ_1, …, χ_(r+1))`. `IsSubquotientOf` means that
    some subrepresentation maps onto `π`.

`UnramifiedSphericalVectorStatement` (§1.3). For every `p`, `F`, `r`, every
representation `π` of `GL_(r+1)(F)` and every `ψ` with `HasIntegerConductor ψ`
(`ψ` trivial on `O` and on no larger fractional ideal), suppose `π` is generic
for `ψ` and has a nonzero `GL_(r+1)(O)`-fixed vector. Then:

- for every nonzero `ℓ` in `glFunctionals ψ r π`, the type `SphericalTest π ℓ`
  has exactly one element;
- the same holds for every nonzero `ℓ` in `glInverseFunctionals ψ r π`, the
  standard Whittaker functionals for `ψ⁻¹`.

`SphericalTest π ℓ` is the published type of right `GL_(r+1)(O)`-invariant
functions `W` in the coefficient model `{g ↦ ℓ(π(g)v)}` of `ℓ` with
`W(e) = 1`.

`UnramifiedPairIntegralStatement` (§1.4 (3)). Take `r = n + k + 2` and
`r' = n + 1`. The rank of `π` is written `n + (0 + k + 1) + 1` to match the
published `j = 0` block of the JPSS integrals. Let `π` and `σ` be
representations of `GL_r(F)` and `GL_(r')(F)`, and let `χ`, `χ'` be tuples of
quasi-characters with `IsUnramifiedGenericConstituent F ψ π χ` and
`IsUnramifiedGenericConstituent F ψ σ χ'`. Let `q`, `abv`, `ϖ` and `μ` satisfy
the published `IsJacquetNormalization q ψ abv ϖ μ`:

- `q` is the residue cardinality;
- `ϖ` is a uniformizing element;
- `abv` is the normalized absolute value: `|ϖ| = q⁻¹`, and `abv` is trivial on
  valuation units;
- `ψ` has conductor `O`;
- `μ` on `N_(r') \ GL_(r')` is compatible with the Haar measures
  `generalLinearHaar` (`GL_(r')(O)` of mass one) and `unipotentHaar`
  (`N_(r')(O)` of mass one).

Let `ℓ` be a nonzero `ψ`-Whittaker functional on `π` and `ℓ'` a nonzero
`ψ⁻¹`-Whittaker functional on `σ`. Let `w`, `w'` be any elements of
`SphericalTest π ℓ` and `SphericalTest σ ℓ'`. Then there is a real `c` such
that, for every `s` with `Re s > c`, two things hold:

- `UnequalRankConverges ψ abv 0 k μ (dirac 0) w w' s` holds;
- `unequalRankModelIntegral ψ abv 0 k μ (dirac 0) π σ ℓ ℓ' w w' s` equals
  `unramifiedEulerFactor q (unramifiedClass F χ) (unramifiedClass F χ') s`.

The first item says that the integral converges absolutely. For `j = 0` the
rectangular variable is a point carrying the measure `dirac 0`. The published
integral is then `∫_(N_(r') \ GL_(r')) w(diag(g, 1_(k+1))) w'(g)
|det g|^(s-(k+1)/2) dμ(g)`, with `abv` as the absolute value.

`UnramifiedUnitaryPoleFreeStatement` (Proposition 1.5(iii)). Let `n < t`.
Let `π` of `GL_(t+1)(F)` and `σ` of `GL_(n+1)(F)` satisfy
`IsUnramifiedGenericConstituent` for some `ψ` with tuples `χ`, `χ'`, and let
both be `IsUnitarizable`, that is, have an invariant positive definite
Hermitian form. Then for every `s` with `Re s ≥ 1`,
`∏_i ∏_j (1 - χ_i(ϖ) χ'_j(ϖ) q^(-s)) ≠ 0`, where `q` is
`F.canonicalTopologicalData.residueCardinality`. That is,
`det(1 - A ⊗ A' q^(-s))⁻¹` has no pole there.

`UnramifiedPairStatement` is the conjunction of the three statements.

## Interpretation

- **Uniqueness and nonvanishing (§1.3).** The Lean statement asserts that
  exactly one normalized spherical vector exists. This is equivalent to the
  source's two claims: that the right `K`-invariant vectors form a line, and
  that `W_0(e) ≠ 0`. Suppose the normalized spherical vector `W_0` is unique.
  If a nonzero spherical `W` had `W(e) = 0`, then `W_0 + W` would be a second
  normalized one. So every spherical `W` equals `W(e) W_0`. The converse is
  immediate.
- **The `ψ⁻¹` clause.** `ψ⁻¹` also has conductor `O`, and `π` is generic for
  `ψ⁻¹` exactly when it is generic for `ψ`. The second clause is §1.3 applied
  to `ψ⁻¹`. The `ψ⁻¹`-models carry the second member of each JPSS pair.
- **Unramified and generic.** In §1.3 "unramified" means containing the
  trivial representation of `K`, which is the fixed-vector condition. §1.3 and
  §1.4 work with generic representations: the essential element lives in
  `𝒲(π; ψ)`. So genericity is a hypothesis. Every model of a nonzero
  functional is quantified over, which is harmless: §1.1 says the functional
  is unique up to scalars, so the coefficient model is `𝒲(π; ψ)` for every
  nonzero `ℓ`.
- **The class `A`.** The source attaches `A` to `π` through an induced
  representation of which `π` is the unique unramified component. The
  predicate `IsUnramifiedGenericConstituent` asks for unramified `χ_i` with
  `π` a subquotient of `i(χ)` that has nonzero `K`-fixed vectors. By the
  Iwasawa decomposition, the `K`-fixed space of `i(χ)` is one-dimensional, so
  `i(χ)` has exactly one irreducible subquotient with `K`-fixed vectors. Hence
  this predicate pins `π` as the unique unramified component. Conversely,
  the unramified `χ` with this property are determined by `π` up to order.
  This is the parametrization by semisimple classes recalled in §1.3. The
  products in the conclusions do not depend on the order, so every admissible
  choice of `χ` gives the same statement. For unramified `χ_i` the value
  `χ_i(ϖ)` does not depend on the uniformizer. So the canonical uniformizer in
  `unramifiedClass` and the `ϖ` of `IsJacquetNormalization` may differ.
- **Normalized induction.** The source writes `Ind(G_r, B_r; μ_1, …, μ_r)`
  without fixing the normalization. Formula (3) forces normalized induction,
  which is what the published `principalSeries` uses. A check for
  `GL_2 × GL_1` uses the Casselman-Shalika-Shintani formula
  `W_0(diag(ϖ^m, 1)) = q^(-m/2) h_m(A)` for the normalized class: the integral
  is `Σ_m h_m(A) (b q^(-s))^m = ∏_i (1 - a_i b q^(-s))⁻¹`, where `h_m` is the
  complete symmetric polynomial and `b = A'`.
- **`ε` and the `ψ⁻¹`-model.** The source integrates `W'(εg)` with `W'` the
  essential element of `𝒲(π'; ψ)`. For `ε = diag(1, -1, 1, …)` one has
  `ε n ε⁻¹` equal to `n` with its superdiagonal negated. So
  `g ↦ W'(εg)` transforms under `N_(r')` by `ψ⁻¹`. It is right `K`-invariant
  because `ε ∈ K`, and it takes the value `W'(ε) = W'(e) = 1` at `e`. It is
  therefore the normalized spherical vector of the `ψ⁻¹`-model of `π'`, which
  is the vector `w'` of the Lean statement. The JPSS integrals of the Library
  use the `ψ⁻¹`-model directly, so the Lean integral is the source's
  `Ψ(s, W, W')`. The source calls `ε` "a row vector of length `r`". The sign
  computation above needs it to be the diagonal matrix of size `r'` that
  multiplies `g ∈ G_(r')`, and that is how it is read here.
- **Measures and normalizations.** The source normalizes `dg` as the quotient
  of the Haar measures of `G_(r')` and `N_(r')` that give `K` and `K ∩ N_(r')`
  volume one. This is the `measure` field of `IsJacquetNormalization`, whose
  other fields fix `q`, the absolute value and the conductor of `ψ`, as in
  §0.3 and §1.4.
- **Convergence.** "Converges for `Re(s)` large" is read as absolute
  convergence (the gauge majorization gives absolute convergence) on a half
  plane `Re s > c`, on which identity (3) holds. The value of `c` is not
  specified, as in the source.
- **Proposition 1.5(iii).** The source's setting is `r > r'` ("with the above
  notations"), hence `n < t`. Its proof derives (iii) from the convergence (ii)
  of the integral at the essential elements, so `π` and `π'` must be generic.
  Without genericity the statement would fail: the trivial representations of
  `GL_3(F)` and `GL_1(F)` are unitary and unramified with
  `A = diag(q, 1, q⁻¹)` and `A' = 1`, and the factor `1 - q · q^(-s)`
  vanishes at `s = 1`. "Unitary" is `IsUnitarizable`, the existence of an
  invariant positive definite Hermitian form. For irreducible admissible
  representations this is unitarity in the source's sense. "No pole" is
  stated as nonvanishing of the product, whose inverse is the Euler factor.
- **Field.** `F` is a p-adic field because `sphericalSubgroup`,
  `principalSeries` and the canonical topological data are published only for
  `PadicField`. The source allows any non-archimedean local field.
- **Not stated.** Not stated here:
  - the equal-rank case `r = r'`, which uses part I, Proposition (2.3), a
    source not in the project literature;
  - that the JPSS L-factor of an unramified generic pair equals this Euler
    factor (the source *defines* `L(s, π × π')` as the Euler factor);
  - Proposition 1.5(i) and (ii);
  - the archimedean Section 2.

## Universes

`unramifiedClass` and `IsUnramifiedGenericConstituent` have universe
parameters `uF` (the field), and `IsUnramifiedGenericConstituent` also `uV`
(the space of `π`). `UnramifiedSphericalVectorStatement` has `uF` and `uV`.
`UnramifiedPairIntegralStatement`, `UnramifiedUnitaryPoleFreeStatement` and
`UnramifiedPairStatement` have `uF`, `uV` (the space of `π`) and `uW` (the
space of `σ`).
