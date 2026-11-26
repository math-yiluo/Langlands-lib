# The joint continuation of the cuspidal-pair Eisenstein series at universe 0

Module `Langlands.Global.Factors.CuspidalPairEisensteinJointContinuationReduction` states and
proves `Langlands.Global.CuspidalPairEisenstein.CuspidalPairEisensteinJointContinuationReductionStatement`.

## Statement

The four premises

- `EisensteinMeromorphicContinuationStatement.{0}` (Bernstein–Lapid, Theorem 2.3 (1)),
- `EisensteinJointRootHyperplaneStatement.{0}` (Bernstein–Lapid, Theorem 2.3 (1) and (6), with the
  Corollary in §8.6),
- `EisensteinImaginaryAxisHolomorphyStatement` (Lapid 2011, Proposition 6), and
- `CuspidalPairSquareIntegrableTwistStatement` (module
  `Langlands.Global.Factors.CuspidalPairSquareIntegrableTwistStatement`)

imply `CuspidalPairEisensteinJointContinuationStatement.{0}`. That is the joint continuation of
the cuspidal-pair Eisenstein series, with holomorphy on `Re s = 0`, for every number field
`F : Type`. The module does not prove the four premises.

## Why universe 0

`CuspidalPairEisensteinJointContinuationStatement` is universe-polymorphic. The reduction reaches
its instance at universe `0`, for number fields `F : Type`. The reason is that
`IsSquareIntegrableInducedForm` (Lapid's `A^2_P`, module
`Langlands.Global.AdelicSquareIntegrableInducedForms`) and the measure
`RestrictionSplitCentre.canonicalMeasure` it integrates against are defined for `F : Type` only:
the Weil restriction to `ℚ` is taken inside one universe. So
`EisensteinImaginaryAxisHolomorphyStatement` and `CuspidalPairSquareIntegrableTwistStatement` are
stated for `F : Type`.

Universe `0` enters the proof only inside the argument for clause 3, through the two premises
that rest on `IsSquareIntegrableInducedForm`: `CuspidalPairSquareIntegrableTwistStatement` gives
the square-integrable form `ψ`, and `EisensteinImaginaryAxisHolomorphyStatement` is applied to it.
Everything else is proved for `F : Type u` in an arbitrary universe:

- the comparison with the group-scheme objects (`CuspidalPairSchemeComparisonStatement`);
- the regularity of the line (`CuspidalPairLineRegularityStatement`);
- the first two clauses, from the first two premises (`CuspidalPairEisensteinLineReductionStatement`,
  module `Langlands.Global.Factors.CuspidalPairEisensteinLineContinuation`);
- the passage from `ψ` to its imaginary twist `ψ m_P^{iy}`
  (`EisensteinLine.hasImaginaryAxisHolomorphy_of_eq_mul_heightPower`).

An assembly in an arbitrary universe `u` needs both square-integrability-based premises, the
imaginary-axis statement and the square-integrable twist, stated and proved in that universe.
With them, the same proof gives `CuspidalPairEisensteinJointContinuationStatement.{u}`.

Consumers of these statements use them for the universe of their own number field. These are:

- `cuspidalPairEisensteinHolomorphyReduction` (`CuspidalPairEisensteinJointContinuationStatement.{u}`
  to `CuspidalPairEisensteinHolomorphyStatement.{u}`);
- `cuspidalPairBoundaryNonvanishingEnlarged_of_eisenstein` and `cuspidalPairEisensteinDerivation`
  (`CuspidalPairEisensteinHolomorphyStatement.{u}`, together with the separate premise
  `CuspidalPairEisensteinCoefficientStatement.{u, uQ}`, to
  `CuspidalPairBoundaryNonvanishingEnlargedStatement.{u, uQ}` and
  `CuspidalPairBoundaryNonvanishingStatement.{u, uQ}`);
- `cuspidalIsobaricPoleOrderReduction` and `cyclicCuspidalFiberReduction` (from
  `CuspidalPairBoundaryNonvanishingStatement` at the universe of the number field).

From this reduction they receive their instances for number fields `F : Type` only. With
`cuspidalPairEisensteinHolomorphyReduction.{0}`, the four premises give
`CuspidalPairEisensteinHolomorphyStatement.{0}`.

## Implemented proof

`cuspidalPairEisensteinJointContinuationReduction`:

1. `cuspidalPairEisensteinLineReduction.{0}`, applied to the first two premises, gives `E` and `σ`
   with clauses 1 and 2 of the target. It also gives clause 3 under the hypothesis that the
   group-scheme Eisenstein series of `φ ∘ adelicHomeomorph F N` has
   `EisensteinLine.HasImaginaryAxisHolomorphy` (the conclusion of Lapid's Proposition 6, for the
   block parabolic, `blockRootData` and the standard maximal compact subgroup).
2. `CuspidalPairSquareIntegrableTwistStatement` gives `y` and `ψ ∈ A^2_P` with
   `φ ∘ adelicHomeomorph = ψ · m_P^{iy}`.
3. `EisensteinImaginaryAxisHolomorphyStatement`, applied to `ψ`, gives
   `HasImaginaryAxisHolomorphy` for `ψ`. It is applied to the scheme `GL_N`, which is connected
   reductive, with the block parabolic, its geometric unipotent radical, the block Levi,
   `blockRootData`, the standard maximal compact subgroup and the standard closed embedding.
   Steps 2 and 3 are the only uses of universe `0`.
4. `EisensteinLine.hasImaginaryAxisHolomorphy_of_eq_mul_heightPower` transfers it to
   `φ ∘ adelicHomeomorph`. Clause 3 of the target follows from step 1.

## Provenance

The target is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
II.1.5, IV.1.8, IV.1.9 (b)–(d) and IV.1.11 (a)–(b), for the cuspidal datum
`(GL_(r+1) × GL_(t+1), π ⊗ (π')^∨)` on Shahidi's line (see
`CuspidalPairEisensteinJointContinuationStatement.md`). The reduction follows the group-scheme
route described there:

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math.
  Soc. 37 (2024), Theorem 2.3 (1) and (6) (p. 191), for the continuation and its root
  hyperplanes;
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*, Clay
  Math. Proc. 13 (2011), Proposition 6 (p. 329), for the imaginary axis;
- Lapid's §2 (p. 311), decomposition (1), for the exponential twist `e^{⟨iy, H_P⟩}` of a
  normalized form in `A^n_P`;
- Mœglin–Waldspurger I.2.18 (p. 39), for the square integrability of cusp forms with unitary
  central character, the separate input that puts the normalized form in `A^2_P`.
