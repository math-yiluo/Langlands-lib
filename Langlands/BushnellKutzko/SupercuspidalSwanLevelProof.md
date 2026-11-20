# The Swan conductor of a supercuspidal is rank times normalized level

Worker 408 authored the Lean proof. Worker 302 prepared it for Task 7683.

## Statement

`Langlands.BushnellKutzko.supercuspidalSwanLevel` has type
`Langlands.BushnellKutzko.SupercuspidalSwanLevelStatement.{uK, uV}`. For every prime `p`,
`K : PadicField.{uK} p`, `k : ℕ`, and supercuspidal class `π` of `GL_{k+1}(K)` with
carrier universe `uV`, suppose `x : ℚ` is a normalized level of
`Correspondence.supercuspidalToAutomorphic K π`. The proof gives `c : ℕ` with
`Henniart.Numerical.conductor K π = (c : WithTop ℕ)` and
`((c - (k + 1) : ℕ) : ℚ) = ((k + 1 : ℕ) : ℚ) * x`.

The statement identifies the Swan conductor by truncated subtraction. In rank one, if `c = 0`
then `x = 0`. In ranks at least two, the additive character and self-dual measure used in the
calculation are chosen within the proof.

## Proof

- For `k = 0`, the first fixed level is finite because the representation has a normalized
  level value. For a lattice chain of period `e`, a fixed vector at `U^{m+1}` is fixed by the
  congruence subgroup at level `⌊m/e⌋ + 1`. Conversely, a fixed vector at congruence level `c`
  is fixed by `U^{max(c,1)}` of the period-one standard chain. These give `c - 1 ≤ x` and
  `x ≤ c - 1` in `ℚ`, with subtraction in `ℕ`. [Rank-one proof](SwanLevelRankOne.md)
- For `k > 0`, write `N = k + 1` and choose a unitary additive character `ψ` of conductor
  `𝔬_K` and a self-dual Haar measure `ν`. The Library theorem
  `GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData` supplies the
  normalized matrix functional equation, with both Euler polynomials `1`, a complex unit and
  an integer exponent `a`. The stratum calculation gives `max(a, N) = N(1 + x)` in `ℚ`.
  [Exponent calculation](ConductorFormula.md)
- With the same `ψ` and `ν`, the actual Whittaker model coefficient inclusion lets
  `RankinSelberg.rankOneAmbientMatrixFunctionalEquationComparison` identify the rational
  gamma factor against the trivial `GL_1` character. This theorem supplies the normalized
  comparison described in the statement documentation. Both Rankin–Selberg L-polynomials are
  `1`. The additive conductor of `ψ` is zero, so the JPSS epsilon exponent is the newvector
  level by `Conductor.supercuspidalPadicConductorExponent`. Equality of the two monomials
  gives `a = c`, where `c` is the first fixed level. [Conductor comparison](ConductorBridge.md)
- The maximum identity then gives `c - N = N x` with truncated subtraction. At level zero it
  gives `c ≤ N`, which suffices for Swan conductor zero. [Higher-rank proof](SwanLevelHigherRank.md)

## Stratum and determinant-shell calculation

At a positive attained level `x = m/e`, a fixed vector for `U^{m+1}` yields an eigenvector of
`U^m/U^{m+1}`. Finite additive duality realizes its character by a representative `b` in
`𝔓^{-m}`. Moy's reduction shows that a nilpotent leading term in `b + 𝔓^{1-m}` would give a
smaller level. This uses the Library's splitting basis and filtration coordinates. The
openness and compactness of `U^m` come from `FundamentalStratumLevelCore` of Task 7681.
[Moy's reduction](MoyReduction.md), [minimality](LevelAttainingStratum.md),
[stratum existence](StratumExistence.md)

A character-twisted indicator gives a nonzero constant matrix zeta value. Trace duality
restricts the Fourier transform to a matrix coset. Extracting the coefficient on the
shell `ord(det g) = -a` gives a point where both the Fourier transform and the dual
coefficient are nonzero. Its determinant yields the upper bound. A fixed vector for `U^1`
gives the upper bound at level zero.
[Trace duality](TraceDuality.md), [Fourier support](FourierSupport.md),
[stratum test](StratumZetaIntegral.md), [shell identity](ShellIdentity.md),
[upper bound](ConductorUpperBound.md)

At positive level, translating the smooth functional lets the shell argument be iterated
while preserving a nonzero matrix coefficient on the product. Products in the stratum coset
have controlled filtration, and compact support modulo the centre bounds their determinant
orders. This yields the reverse inequality `a ≥ N(1 + x)`.
[Determinant estimates](CompactLevelBound.md), [lower bound](ConductorLowerBound.md)

## Provenance

- The operator route note (16 November 2026), Proposition 4.6 (`prop:T2`), §4.4 and
  Lemma 4.11(i) (`lem:level`), printed pp. 12 and 15–16, gives the Swan formula and its
  normalized-level interpretation. Registered as `operator-numerical-llc-route-2026-11-16`.
- Bushnell (1987), Theorems 1 and 2′(ii), printed pp. 192 and 196–197, supplies the stratum
  reduction and existence route. Theorem 3 and (3.5)–(3.8), printed pp. 198–199, give the
  conductor formula through nondegenerate representations of order normalizers. Registered
  as `bushnell-1987-hereditary-orders-gauss-sums`.
- Bushnell–Fröhlich (1985), (3.3.8)(iv), printed p. 258, gives the local constant through a
  nonabelian congruence Gauss sum. The Lean proof obtains the exponent by the determinant-shell
  calculation above. Registered as `bushnell-frohlich-1985-nonabelian-congruence-gauss-sums`.
- Bushnell–Kutzko (1993), (1.1.2), (1.1.4)–(1.1.6) and (2.3.1), printed pp. 20–22 and 57,
  gives the lattice-chain, trace-duality and reduction conventions. Registered as
  `bushnell-kutzko-1993-admissible-dual-gln`.
- Jacquet–Piatetski-Shapiro–Shalika (1981), §(5.1), printed p. 211, relates the epsilon
  exponent at additive conductor zero to the first fixed level. The Library supplies its
  p-adic supercuspidal case. Registered as `jpss-1981-conductor`.
