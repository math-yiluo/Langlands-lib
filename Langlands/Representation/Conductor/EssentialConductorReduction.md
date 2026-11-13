# The essential-vector and conductor theorems from their inputs

This internal unit assembles the target of Task 5032,
`Langlands.Conductor.EssentialConductorStatement` (Jacquet 2012, Theorem 1 with its
uniqueness clause, printed page 517; JPSS 1981, Theorem (5.1), printed page 211). It
proves the target from five inputs, which are hypotheses of the final theorem
`essentialConductorStatement_of`. No instance of any input is claimed here.

- `hex : EssentialVectorExistence`, defined in this module: the existence half of the
  published `EssentialVectorStatement`.
- `hmir : MirabolicRestrictionInjectivityStatement` (published statement, Jacquet and
  Shalika 1981, Section 1.1).
- `hdual : EssentialDualComparisonStatement` (published statement, JPSS 1981 (5.3)).
- `hmin : ConductorMinimalityStatement` (published statement, JPSS 1981, proof of
  Theorem (5.1)).
- `heps : TrivialCharacterEpsilonStatement` (published statement, JPSS 1983, Theorem
  (2.7), for `π` against the trivial character of `GL_1`).

The published theorems `essentialIntegralLastRowSupport` (integral last-row support of
the essential vector) and `GodementJacquet.localTateConductor` (scalar Tate theory over
any nonarchimedean local field) are used directly. All five inputs are quantified at the
universes `uF, uV` of the target.

## The existence predicate

`EssentialVectorExistence` has exactly the binders of the published
`EssentialVectorStatement`: a nonarchimedean local field `F`, `n`, the measurable
structures, Jacquet's normalizations `h : IsJacquetNormalization q ψ abv ϖ μ`, a
representation `π` of `GL_(n+2)(F)` with `IsGeneric ψ (n + 1) π`, and `ℓ` with
`ℓ.val ≠ 0`. Its conclusion is `∃ w, IsEssentialVector h π ℓ w` instead of `∃!`. It is the
existence half of Jacquet 2012, Theorem 1. The staged unit
`Conductor/EssentialExistenceReduction` (candidate 960ef4cb) proves it for each `π` from
the JPSS 1983 inputs. Those inputs are not yet available over arbitrary `F`.

## Results

- `essentialVectorStatement_of_existence`: `hex` and `hmir` give
  `EssentialVectorStatement`. Existence comes from `hex`. Uniqueness is the published
  `existsUnique_isEssentialVector_of_exists`, with injectivity from `hmir` at rank
  `n + 2`; genericity supplies smoothness.
- `IsEssentialVector.mem_jacquetFixedVectors` and
  `IsEssentialVector.right_jacquet_invariant`: under `hmir`, an essential vector of a
  generic `π` is fixed by the integral Jacquet mirabolic
  `fieldJacquetMirabolic O (n + 1)`. Its restriction to `diag(GL_(n+1), 1)` is right
  `GL_(n+1)(O)`-invariant (part of `IsEssentialVector`) and is supported on integral
  last rows (`essentialIntegralLastRowSupport`). The published
  `mem_jacquetFixedVectors_of_integral_restriction` then applies. This is JPSS 1981,
  (5.2), printed pages 211-212 (invariance under `H(0)`).
- `essentialVectorLevelStatement_of`: `hex`, `hmir` and `hdual` give
  `EssentialVectorLevelStatement`. Let `c q^(-ms)` be the epsilon factor, with `m` a
  natural number. The dual representation `inverseTransposePullback π` is
  `ψ.scale (-1)`-generic (`isGeneric_inverseTransposePullback`). Jacquet's normalizations
  pass to `ψ.scale (-1)` (`IsJacquetNormalization.scaleNegOne`), and the dual functional
  is nonzero (`scaledDualFunctional_ne_zero`). So `hex` supplies an essential vector `w'`
  of the dual. `hdual` gives `C` with `W̃(g) = C w'(g diag(ϖ^m, …, ϖ^m, 1))`. Both
  functions are invariant under the integral Jacquet mirabolic (previous item, applied to
  `π` and to its dual). The published
  `mem_levelFixedVectors_of_rankInclusion_dual_comparison` puts `w` in the level-`m` fixed
  space. This is the argument of JPSS 1981, (5.2) and (5.3), printed pages 211-213.
- `conductorExponentStatement_of`: all five inputs give `ConductorExponentStatement`.
  - Rank one (`n = 0`) is the published `conductorExponent_rankOne_of_localTate` with
    `GodementJacquet.localTateConductor`.
  - Rank `k + 2`. `ConductorExponentStatement` does not supply the measurable structures
    on `GL_(k+1)(F)`, its unipotent subgroup and the quotient. The proof equips them with
    their Borel σ-algebras and takes the published compatible quotient measure
    `unipotentQuotientHaar F k` (`unipotentQuotientHaar_isCompatible`). Together with the
    given `q`, `ϖ`, `abv` and `ψ` this is a Jacquet normalization `h`.
  - `heps` gives the epsilon factor `c q^(-ms)` with `m ∈ ℤ`, and genericity gives a
    nonzero functional `ℓ`. `hex` gives an essential vector `w`, unique by `hmir`.
  - With the dual essential vector and `hdual` as above, the published
    `right_level_toNat_invariant_of_dual_comparison` shows `0 ≤ m`. It needs `w ≠ 0`
    (`IsEssentialVector.ne_zero`) and the invariances of the previous items, and its
    route is `hasJacquetDualComparison_of_rankInclusion_scalar` and
    `right_invariant_central_translate`. Write `m = a` with `a` a natural number.
  - `w` is fixed at level `a` by `essentialVectorLevelStatement_of`. `IsEssentialVector`
    contains an L-polynomial `P` with `IsCharacterLPolynomial`, so `hmin` applies to
    every level-`b` fixed vector `v`. If `v ≠ 0` then `a ≤ b`, so there is no nonzero
    fixed vector below level `a`. At level `a`, every fixed vector satisfies Jacquet's
    identity scaled by some `C`, so it equals `C w` (published
    `exists_eq_smul_of_mem_levelFixedVectors`, using uniqueness). Thus `w` spans a level
    line (`IsLevelLine`).
  - The published `isNewvectorConductor_and_finrank_of_essential` transfers this to `π`:
    `IsNewvectorConductor π a` and `finrank (levelFixedVectors π a) = 1`. This is JPSS
    1981, (5.3), printed pages 213-214.
- `essentialConductorStatement_of`: the conjunction of the three results above is
  `EssentialConductorStatement`.
