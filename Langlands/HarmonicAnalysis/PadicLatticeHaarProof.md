# Valuation-lattice Haar masses and conductor normalization

Author: Worker 450.

The theorem `Langlands.HarmonicAnalysis.padicLatticeHaar.{u}` proves exactly
the published
`Langlands.HarmonicAnalysis.PadicLatticeHaarStatement F T`.
Its complete telescope is

```lean
{p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p)
  (T : F.TopologicalData)
```

The field universe `u` is arbitrary, and every supplied topology `T` and
every integer lattice level are covered. The theorem has no additional
hypotheses. The target and all its imported Lean/Markdown pairs are
preserved.

## Objects and conventions

The proof installs `T.topology`, `T.valuativeRel`, `T.localField`, and that
topology's Borel measurable space and certificate, as the target does.
Write `O = T.Integers`, `q = T.residueCardinality` cast to `ℝ`, and
`L m = T.additiveLattice m = π^(-m) O`. All powers indexed by integers are
`zpow`, including negative levels and negative conductors.

The measures are the existing `AdditiveHaarMeasure F.Carrier` bundles:
their underlying measures are additive Haar measures and regular.
The character `ψ` in the second conjunct is the existing continuous,
nontrivial, unit-circle-valued `UnitaryAdditiveCharacter F.Carrier`;
its conductor is the actual integer `T.additiveConductor ψ`.

## Implemented proof

The private helper `latticeHaarMass` proves the first conjunct.
The imported published lemmas `T.isCompact_additiveLattice m` and
`T.isOpen_additiveLattice m` apply to the supplied topology and all integer
levels. Compactness gives

```text
μ.measure (L m) < ∞.
```

Openness and membership of zero give strictly positive extended-real mass.
Together these imply strictly positive `toReal` mass through
`ENNReal.toReal_pos`. Thus finiteness is established before the real-valued
mass is used.

For the scaling formula let `a = (uniformizerUnit T)^m`. The published
`T.mem_additiveLattice_iff_div_mem_integers` identifies

```text
{x | a*x ∈ O} = L m.
```

Apply `padicScalarHaarScaling F T μ.measure a` and evaluate both sides on
the open, hence measurable, set `O`. The pushforward on the left evaluates
to `μ.measure (L m)`. The right is the original mass of `O` multiplied
by the inverse normalized absolute value of `a`. The published
`uniformizerUnit_zpow_abs T m` gives `|a| = q^(-m)`, so this inverse is
`q^m`. Applying `toReal`, its multiplication rule, and
`T.mem_additiveLattice_zero` gives

```text
(μ.measure (L m)).toReal = q^m * (μ.measure (L 0)).toReal.
```

The closing theorem uses this helper for its first conjunct. For a given
`ψ`, set `n = T.additiveConductor ψ`. The compact open integer ring has
nonempty interior, so it defines a `TopologicalSpace.PositiveCompacts`
object `K`. After installing the supplied Hausdorff certificate
`T.fieldT2`, construct

```text
μ = normalizedAdditiveHaar F.Carrier K.
```

Mathlib's `Measure.addHaarMeasure_self` gives `μ.measure O = 1`.
The actual residue cardinality satisfies `q > 1`; hence `q^n > 0` and
`sqrt(q^n) > 0`. Define the nonzero nonnegative real scalar

```text
c = 1 / Real.sqrt (q^n).
```

The measure `c • μ.measure` is an additive Haar measure by
`Measure.IsAddHaarMeasure.nnreal_smul`, and regularity follows from the
regularity instance for scaling by a nonnegative real. These certificates
form the required bundle `ν`.

The helper's scaling formula for `μ`, its level-zero mass one, and the
evaluation rule for scaled measures give, for all integers `m`,

```text
(ν.measure (L m)).toReal = q^m / Real.sqrt (q^n).
```

For the second mass identity, substitute this formula at `m` and `n-m`.
The numerator multiplies to `q^(m+(n-m)) = q^n`, using the nonzero base
`q`. The denominator is `sqrt(q^n)^2 = q^n`, using positivity. Cancelling
the nonzero `q^n` proves that the product is one. No parity restriction on
`n` or division of an integer exponent is needed.

## Dependencies and provenance

This is a derived proof of the existing target, using the existing
valuation lattices and Haar construction. It introduces no new statement
interface or normalization convention.

- [PadicLatticeGeometryProof](PadicLatticeGeometryProof.md) imports the
  supplied-topology compact/open lattice lemmas proved by Worker 252 in
  `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`.
- [PadicScalarHaarScalingProof](PadicScalarHaarScalingProof.md), by
  Worker 90, supplies the scalar pushforward formula, compactness and
  openness of `O`, and intrinsic regularity.
- [Uniformizer](../LocalField/Uniformizer.md) supplies the existing chosen
  uniformizer as a field unit and its integer-power absolute value.
- [Basic](Basic.md) supplies the actual character and regular additive
  Haar bundles and `normalizedAdditiveHaar`.

No Fourier inversion, self-dual measure existence, local-factor functional
equation, or theorem requiring `IsSelfDual` is used. The conclusion is Haar
volume normalization only. In particular it asserts neither self-duality
nor uniqueness of the constructed measure.

The original passages underlying the target were read from these
registered retained sources:

- André Weil, *Basic Number Theory*, second edition (1973), source
  `weil-1973-basic-number-theory`, retained file
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
  SHA-256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`:
  Chapter I §2, printed p.4 (PDF p.21), defines the module by
  `μ(aX) = mod(a) μ(X)`; Chapter I §4, Theorem 6 and Definition 3,
  printed pp.12–13 (PDF pp.29–30), gives `mod(π) = q^(-1)` and the ideal
  powers. Chapter II §5, Definition 4, printed p.41 (PDF p.58), fixes the
  same conductor convention. Chapter VII §2, Corollary 3, printed p.108
  (PDF p.125), gives self-dual integer-ring volume `q^(-n/2)`.
  That last passage explains the chosen numerical normalization;
  its self-duality assertion is not an input or conclusion of this proof.
- John Tate, *Number theoretic background* (1979), source
  `tate-1979-number-theoretic-background`, retained file
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
  (3.2.6), printed p.13 (PDF p.22), fixes the conductor sign. Section 3.6,
  printed p.17 (PDF p.26), was read together with the published
  [scalar-measure correction](../LocalFactor/Harmonic/Statement.md).
  Tate's printed scalar-ratio exponent after (3.6.2) has the opposite sign
  from the correction supported by Weil's normalization; this proof uses
  no scalar-ratio formula from that sentence.

No source-specific Weil or Tate errata file was present in the checked
project/Library notes or retained literature locations on 2026-10-28.
The proof follows the direct positive-rescaling construction above.

## Verification

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The complete unapplied theorem is assigned to the dependent function type
with implicit prime and primality instance followed by explicit `F` and
`T`; declaration inspection checks its universe parameter and axioms.
Formal exact-target validation and independent semantic review are separate
publication checks.
