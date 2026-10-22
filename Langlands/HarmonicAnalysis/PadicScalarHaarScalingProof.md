# Residue-normalized scalar Haar scaling

Author: Worker 90.

This module proves the existing proposition
`Langlands.HarmonicAnalysis.PadicScalarHaarScalingStatement.{uF}` without changing
its statement or imported definitions. The field universe remains arbitrary.
The application theorem is
`Langlands.HarmonicAnalysis.padicScalarHaarScaling`; the closing theorem
`Langlands.HarmonicAnalysis.padicScalarHaarScalingStatement` has exactly the
published proposition as its complete type.

For a prime `p`, a `PadicField p`, supplied topological data `T`, any Borel
measurable structure for exactly `T.topology`, any additive Haar measure `μ`,
and any field unit `a`, the application theorem gives

`μ.map (fun x => (a : F.Carrier) * x) = ((T.normalizedAbsUnits a : ℝ≥0)⁻¹) • μ`.

The theorem adds no regularity, countability, normalization or field-realization
premise. A field unit here is any nonzero field element, not necessarily a unit
of the integer ring. The scalar is the published residue-normalized absolute
value.

## Intrinsic topology API

The following lemmas are public in
`Langlands.PadicField.TopologicalData`, with `T` as argument. Each installs
exactly `T.topology` in its conclusion.

- `sigmaCompactSpace` and `secondCountableTopology` derive the respective
  properties by rewriting the supplied topology to the canonical norm topology.
  The field is finite dimensional over `Padic p`, so Mathlib's
  `FiniteDimensional.proper` supplies properness and the needed instances.
- `pseudoMetrizableSpace` follows from the same topology equality and the
  canonical normed field. Hausdorffness uses the existing `fieldT2` certificate
  from [LocalField/Topology](../LocalField/Topology.md), with the same supplied
  topology and parameter scope.
- `isCompact_integers` and `isOpen_integers` concern the actual set `T.Integers`.
  They use the compact closed valuation ball of radius one and openness of the
  valuation integer ring.
- `haarMeasure_regular` quantifies over the Borel measurable structure and
  additive Haar measure. Sigma compactness, pseudometrizability and local
  finiteness supply regularity through Mathlib's measure instances.

These are lemmas for explicit installation, not new global instances.

## Implemented proof

Write `O = T.Integers`, `q = T.residueCardinality`, and let `π` be the supplied
uniformizer, viewed as a field unit. The remaining helper lemmas are private.

First pull `μ` back to `O` along its measurable subtype embedding. The pullback
is additively translation invariant. The additive subgroup underlying the
maximal ideal has finite index equal to the cardinality of the actual residue
field. `AddSubgroup.index_mul_measure` therefore proves
`q * μ(maximal ideal as a subset of F) = μ(O)`.

Multiplicativity and the integer-ring characterization of `T.normalizedAbs`
identify `a • O` with the closed absolute-value ball of radius `|a|`.
The discrete value group has no value strictly between `exp (-1)` and one;
transporting this fact through the supplied ordered value-group isomorphism
identifies `π • O` with the maximal ideal. The proof handles zero explicitly
and uses the valuation criterion for a nonunit of the integer ring.

The compact open set `O` has positive finite Haar measure. Mathlib's
`MeasureTheory.distribHaarChar_mul`, with the intrinsically derived regularity,
then identifies the Haar character of `π` as `q⁻¹`, by cancelling `μ(O)` in
the finite-index equation. For a general field unit `a`, the balls `a • O`
and `π^(T.ord a) • O` coincide because their normalized absolute values agree.
Cancelling `μ(O)` again identifies their Haar characters. Multiplicativity of
the character and the published formula `|a| = q^(-T.ord a)` yield exactly
`distribHaarChar F.Carrier a = (T.normalizedAbsUnits a : ℝ≥0)`.

Finally, evaluate the pushforward on each measurable set. The preimage under
multiplication by `a` is `a⁻¹ • s`. Applying the character formula and its
compatibility with inversion gives the displayed inverse factor. Measure
extensionality completes the application theorem; the closing theorem merely
introduces the parameters of the existing proposition and applies it.

## Provenance and scope

This is an internal derived proof of the already published scalar prerequisite,
using the existing normalization theory and Mathlib's Haar uniqueness,
finite-index measure formula and local-field topology results. It does not
transcribe a new literature statement or introduce a new normalization. The
rectangular matrix scaling and block-radical product-Haar results remain
separate proof tasks.
