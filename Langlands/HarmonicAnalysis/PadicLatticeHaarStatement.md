# Valuation-lattice Haar masses and conductor normalization

Worker 753 authored this focused proposition definition.
`Langlands.HarmonicAnalysis.PadicLatticeHaarStatement.{u}` has implicit
parameters `{p : ℕ}` and `[Fact p.Prime]`, followed by explicit parameters
`(F : Langlands.PadicField.{u} p)` and `(T : F.TopologicalData)`. It returns
`Prop` for arbitrary field universe `u` and every supplied `T`.

## Local setup

The proposition installs `T.topology`, `T.valuativeRel`, and `T.localField`,
and the Borel measurable space of that topology with its `BorelSpace`
certificate. This is the same topology, local-field data, and Borel space as
[PadicSelfDualMeasureExistsStatement](PadicSelfDualMeasureExistsStatement.md).
That statement also installs a right additive uniform space. This statement
omits it, because none of the objects used here needs a uniform structure.
Local compactness, the Hausdorff property, and the topological-ring structure
come from the supplied local-field data.

Write `L m` for `T.additiveLattice m` from [Conductor](Conductor.md). It is the
additive subgroup of elements `x` with `T.discreteValuation x ≤ exp m`. This is
the fractional ideal `π^(-m) O`. It increases with `m`, and `L 0` is the integer
ring `T.Integers` (`mem_additiveLattice_zero`). Write `q` for
`T.residueCardinality`, the cardinality of the residue field, cast to `ℝ`.
For an additive Haar measure `μ`, write

```text
v_μ(m) = (μ.measure (L m : Set F.Carrier)).toReal.
```

An `AdditiveHaarMeasure F.Carrier` from [Basic](Basic.md) bundles a measure
with `IsAddHaarMeasure` and `Regular` certificates. All powers `q ^ m` with
`m : ℤ` are integer powers (`zpow`), so negative `m` are included.

## Statement

The proposition is a conjunction of two parts.

1. For every `μ : AdditiveHaarMeasure F.Carrier` and every `m : ℤ`,

   ```text
   μ.measure (L m) < ∞,   0 < v_μ(m),   v_μ(m) = q ^ m * v_μ(0).
   ```

   The finiteness conjunct is stated in `ℝ≥0∞`. So the real value `toReal`
   never hides an infinite mass.

2. For every `ψ : UnitaryAdditiveCharacter F.Carrier`, with
   `n = T.additiveConductor ψ`, there exists `ν : AdditiveHaarMeasure F.Carrier`
   such that for every `m : ℤ`,

   ```text
   v_ν(m) = q ^ m / Real.sqrt (q ^ n),   v_ν(m) * v_ν(n - m) = 1.
   ```

The character is the actual bundled continuous nontrivial unit-circle-valued
additive character from `Basic`. The integer `n = T.additiveConductor ψ` is the
largest `n` with `ψ` trivial on all of `L n` (`additiveConductor_spec`). In
particular, the normalized measure gives the integer ring the mass
`v_ν(0) = 1 / √(q ^ n)`, that is `q^(-n/2)`. The square-root form avoids
integer division in the exponent. The first part applied to `ν` shows that
these masses of `ν` are finite. The reciprocal identity pairs `L m` with
`L (n - m)`, which is the annihilator of `L m` under the pairing `ψ(x * y)`.
The statement itself contains no annihilator claim.

No Fourier transform, Fourier inversion, or self-duality appears as a
hypothesis or as a conclusion. The existence in part 2 is only of a regular
additive Haar measure with the stated lattice masses. The statement does not
assert `IsSelfDual ψ ν`, uniqueness of `ν`, or any `SelfDualMeasureExists`
property. It does not choose a character or a measure.

## Derived provenance and scope

This is an internal prerequisite for a proof of
`PadicSelfDualMeasureExistsStatement`. Worker 688 split it from that proof task
(`2be3a65c-9439-43c6-be52-368dd3a8bf98`). It is not a verbatim theorem of one
source. It combines standard facts in the Library's conventions, as follows.

- Part 1 is the module rule `μ(aX) = mod(a) μ(X)` applied to `a = π^(-m)` and
  `X = O`. Here `mod(π^(-m)) = q^m`. Compactness and openness of `O` make
  `μ(O)` finite and positive.
- Part 2 is satisfied by rescaling any Haar measure `μ` by `q^(-n/2) / μ(O)`.
  With part 1 this gives every displayed lattice mass. The reciprocal identity
  is then the arithmetic `q^m · q^(n-m) / q^n = 1`.
- The masses agree with those of Weil's self-dual measure. Weil shows that the
  dual lattice of `L m` is `L (n - m)`, that dual measures give reciprocal
  masses to dual lattices, and that the self-dual measure gives `O` mass
  `q^(-n/2)`. This statement does not assert that agreement.

The intended proof reuses published Library results by name. These are
`padicScalarHaarScaling`, `T.isCompact_integers`, and `T.isOpen_integers` in
[PadicScalarHaarScalingProof](PadicScalarHaarScalingProof.md), and
`normalizedAdditiveHaar` in `Basic`. This module does not restate their targets.
It imports only [Conductor](Conductor.md), which supplies `Basic`, the
normalization definitions, and the local-field definitions.

This statement does not rely on self-dual measure existence or on the larger
`Langlands.LocalFactors.PadicFourierDualityStatement`. It does not rely on
local-factor functional equations or on any scalar or row theorem that assumes
`IsSelfDual`.

## Original sources

- André Weil, *Basic Number Theory*, second edition, Springer, 1973.
  Registered source `weil-1973-basic-number-theory`, retained file
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
  SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
  - Chapter I §2, printed p.4 / PDF p.21: the module `mod_K(a)` with
    `μ(aX) = mod_K(a) μ(X)` for Haar `μ`.
  - Chapter I §4, Theorem 6 and Definition 3, printed pp.12–13 / PDF pp.29–30:
    `mod(π) = q^(-1)`, the ideals `P^n = π^n R`, and the order function.
  - Chapter II §5, Definition 4, printed p.41 / PDF p.58: the order `ν` of a
    nontrivial character is the largest `ν` with `χ` trivial on `P^(-ν)`. This
    is the Library's `T.additiveConductor`, since `L m = P^(-m)`.
  - Chapter II §5, Proposition 12, printed p.42 / PDF p.59: the dual lattice of
    `P^n` is `P^(-n-ν)`, so the dual of `L m` is `L (ν - m)`.
  - Chapter VII §2, Proposition 2 and Corollary 1, printed pp.106–107 /
    PDF pp.123–124: for a compact open subgroup `L` with dual `L*`, the dual
    measure gives `L*` the mass `α(L)^(-1)`.
  - Chapter VII §2, Corollary 3, printed p.108 / PDF p.125: the self-dual
    measure gives `R` the mass `mod(a)^(1/2)` with `ord(a) = ν`, that is
    `q^(-ν/2)`.
- John Tate, *Number theoretic background*, Corvallis Part II (1979).
  Registered source `tate-1979-number-theoretic-background`, retained file
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  - (3.2.6), printed p.13 / PDF p.22, defines `n(ψ)` with the same convention
    as `T.additiveConductor`.
  - §3.6, printed p.17 / PDF p.26, uses self-dual measures. The published
    Markdown of [Local Fourier inversion and Haar normalization](../LocalFactor/Harmonic/Statement.md)
    records a sign discrepancy in Tate's scalar-ratio exponent after (3.6.2),
    checked against Weil VII §2, Corollary 3. This statement keeps that
    correction. It contains no scalar-ratio formula and does not copy Tate's
    printed exponent.

Worker 753 read the Weil and Tate pages cited above. No source-specific errata
file was present in the workspace or public notes. The published scalar-ratio
correction was read. The bundled formulation, the local instance setup, the
explicit finiteness conjunct, and the square-root normalization are derived
Lean packaging, not verbatim source notation.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
This module defines a proposition only and contains no proof of its target.
