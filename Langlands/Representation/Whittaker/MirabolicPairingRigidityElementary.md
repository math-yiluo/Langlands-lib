# Elementary cases of mirabolic twisted pairing rigidity

Author: Worker 806.

This module reduces
`Langlands.Whittaker.MirabolicTwistedPairingRigidityStatement.{uF,uV,uW} F T n`
(from `MirabolicPairingStatement`) to the single case in which both
representations are radical-generated. That case is recorded as the
Prop-valued definition `RadicalGeneratedPairingRigidity`; this module does not
prove it. All declarations live in the namespace
`Langlands.Whittaker.MirabolicRigidity`.

Notation: `P = mirabolic n F` inside `GL_{n+1}(F)`, `U = Mirabolic.radical n F`
(the last column above the diagonal entry), `τ = mirabolicCompactInduced ψ n`,
`q = T.residueCardinality`, `abv = normalizedAbsoluteValue T`, and the
covariance character `χ_s(g) = determinantWeight abv g (-s)`.

## The radical dichotomy

- `IsRadicalTrivial ξ`: `ξ u x = x` for every `u : U` and `x`.
- `IsRadicalGenerated ξ`: the vectors `ξ u x - x` (`u : U`) span the carrier.
- `radicalSpan ξ`: the span of these vectors as a subrepresentation. It is
  stable under `P` because `U` is normal (`Mirabolic.radical_normal`):
  `ξ g (ξ u y - y) = ξ (g u g⁻¹) (ξ g y) - ξ g y`.
- `radicalTrivial_or_radicalGenerated`: for irreducible `ξ`, `radicalSpan ξ` is
  `⊥` (radical-trivial) or `⊤` (radical-generated).

This is the elementary first step of the `Φ⁻`/`Ψ⁻` analysis of
Bernstein–Zelevinsky (1976), §§5.11–5.12, specialized to an irreducible
representation: `radicalSpan ξ = ⊤` says exactly that the radical Jacquet
module `Ψ⁻ξ = ξ/ξ(U)` vanishes.

## Mixed case

`forms_eq_zero_of_trivial_of_generated` and `forms_eq_zero_of_generated_of_trivial`:
if `χ` is `1` on `U` and one representation is radical-trivial while the other is
radical-generated, every `β` in `InvariantBilinear.forms ξ ξ' χ` is zero.
For the first, invariance with `ξ u v = v` gives
`β v (ξ' u y - y) = 0`, so the kernel of `β v` contains the spanning set; the
second is symmetric. `determinantWeight_radical` supplies `χ_s(u) = 1`: radical
elements are upper unipotent (`Mirabolic.radical_le_upperUnipotent`), and
`determinantWeight_unipotent_mul` gives weight one.

## Rank one (`n = 0`)

The group `mirabolic 0 F` is trivial (`Mirabolic.rankOneSubsingleton`). An
irreducible representation of a trivial group has a nonzero vector
(`exists_ne_zero_of_isIrreducible`), its line is a subrepresentation, so it is
one-dimensional (`nonempty_linearEquiv_of_subsingleton`). Evaluation at `1`,
`rankOneEval`, is a linear bijection from the compact model onto `ℂ`; the
inverse sends `c` to the constant function `rankOneConstant ψ c`, which is
covariant because the rank-one character is trivial (`mirabolicCharacter_rankOne`)
and has compact support because the quotient is a subsingleton.
`equivOfSubsingleton` upgrades any linear equivalence to an equivalence of
representations, giving `rankOne_equiv`. Thus the exception set is empty at
`n = 0`, matching the base case `P₁ = {e}` of JPSS p.383.

## Two radical-trivial representations

- `exists_scalar_of_commute`: Schur's lemma
  (`Langlands.countableDimensionalSchur`) for one operator `ρ z` commuting with
  every `ρ g`, on a carrier of rank at most `ℵ₀`.
- `rank_le_aleph0`: an irreducible smooth representation of a separable
  topological group has countable dimension. It is spanned by one orbit
  (`span_range_orbit_eq_top`), which is countable (`countable_range_orbit`).
- `leviScalar a = Mirabolic.levi (scalar a)` is the matrix `diag(a I_n, 1)`.
  Its commutator with any `g` lies in `U = ker Mirabolic.projection`
  (`leviScalar_commutator_mem`), so on a radical-trivial representation
  `ξ (leviScalar a)` commutes with `ξ` (`apply_mul_leviScalar`).
- `det_leviScalar`: its determinant is `a ^ n`. If `abv a = q⁻¹`, then
  `determinantWeight_leviScalar` gives
  `χ_s(leviScalar a) = (spectralPoint q s ^ n)⁻¹`, via
  `determinantWeight_eq_spectralPoint_zpow`.
- `exists_finset_of_radicalTrivial`: for `0 < n`, with Schur scalars `c, c'` of
  `diag(ϖ I_n, 1)` on `ξ` and `ξ'`, a nonzero form gives
  `c c' β v w = (q^{-s})^{-n} β v w` with `β v w ≠ 0`, so `q^{-s}` is an `n`-th
  root of `(c c')⁻¹`. The finite set `E` is the set of these roots
  (`Polynomial.nthRoots`). It depends only on `ξ` and `ξ'`. Every form is zero
  off `E`.

This is the central-character argument of JPSS §1.5, Corollary 2, p.384,
applied directly to `P` (with radical acting trivially) instead of to `GL_n`.

## The remaining case and the reduction

`RadicalGeneratedPairingRigidity.{uF,uV,uW} F T n` is literally
`MirabolicTwistedPairingRigidityStatement.{uF,uV,uW} F T n` with the two
additional premises `IsRadicalGenerated ξ` and `IsRadicalGenerated ξ'`
after irreducibility. It uses the same topology, field instances, form
submodule and spectral point as the statement.

`mirabolicTwistedPairingRigidity_of_radicalGenerated` proves the statement from
this hypothesis. At `n = 0` it takes `E = ∅` and uses `rankOne_equiv`. At
`n = m + 1` it splits by the dichotomy. Two radical-trivial representations use
`exists_finset_of_radicalTrivial` with the uniformizer unit
`LocalFactor.PadicAbelian.uniformizerUnit T` (`T.normalizedAbs_uniformizer`)
and separability of `P`. The subgroup embedding transfers
`T.generalLinearSecondCountableTopology`. The two mixed cases take `E = ∅`. The
radical-generated case is the hypothesis.

## Sources

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
  Convolutions*, Amer. J. Math. 105 (1983), 367–464, registered as
  `jpss-1983-rankin-selberg`; §1.5, Corollary 2, p.384 and the `P₁` base case,
  p.383.
- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
  where F is a non-Archimedean local field*, Russian Math. Surveys 31:3 (1976),
  1–68, registered as `bernstein-zelevinsky-1976-representations-gln`;
  §§5.11–5.12, pp.46–47 (the functors `Ψ⁻`, `Φ⁻`).
