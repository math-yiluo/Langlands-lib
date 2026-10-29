# Row Fourier surjectivity for every supplied p-adic Haar measure

Author: Worker 457.

`Langlands.HarmonicAnalysis.padicRowFourierSurjectivity.{u}` proves the
published [PadicRowFourierSurjectivityStatement](PadicRowFourierSurjectivityStatement.md).
Its complete telescope has implicit `{p : ℕ}` and `[Fact p.Prime]`,
followed by explicit `F : PadicField.{u} p`, `T : F.TopologicalData`, and
`d : ℕ`; its result is exactly `PadicRowFourierSurjectivityStatement F T d`.
The field universe and dimension are unrestricted.

For every continuous nontrivial unitary additive character `ψ`, regular
additive Haar measure `ν`, and actual Schwartz–Bruhat cutoff `Φ` on
`Fin d → F.Carrier`, the theorem supplies an actual Schwartz–Bruhat kernel
`κ` such that

```text
Φ(y) = ∫ x, ψ.complex (∑ i, x i * y i) * κ(x) ∂rowMeasure ν d.
```

The integral uses the published plus pairing and the actual product of
the supplied scalar measure in all coordinates.

## Supplied topology and measurable structures

The proof installs `T.topology`, `T.valuativeRel`, and `T.localField`.
The latter supplies local compactness and the topological ring structure.
It installs the right additive uniform space and the uniform additive
group certificate used by the scalar existence target. The right uniform
space retains the original underlying topology; its topology is
definitionally the supplied topology, so the scalar result applies to
the same characters and measures as the row target.

The scalar measurable space is `borel F.Carrier` for this topology, with
its explicit `BorelSpace` certificate. Hausdorffness comes from
`T.fieldT2`, and second countability from `T.secondCountableTopology`,
imported from [PadicScalarHaarScalingProof](PadicScalarHaarScalingProof.md).
These certificates concern exactly `T.topology`. Mathlib then supplies
the finite product `BorelSpace (Fin d → F.Carrier)` for the product
measurable structure of these scalar Borel spaces.

## Assembly from published proofs

First, [padicSelfDualMeasureExists](PadicSelfDualMeasureExistsProof.md)
provides a total disconnectedness certificate for the supplied topology.
After installing that certificate, its remaining conclusion gives, for
the supplied `ψ`, a regular scalar Haar measure `μ` with `IsSelfDual ψ μ`.
The proof chooses this reference measure; no normalization condition is
imposed on the independently supplied `ν`.

Next, [rowFourierCompatibility](RowFourierCompatibilityProof.md) applied
to `ψ`, `μ`, `d`, and this scalar self-duality proof yields both
`RowFourierClosed ψ μ d` and `IsRowSelfDual ψ μ d`.
Finally, [rowFourierHaarSurjectivity](RowFourierHaarSurjectivityProof.md)
uses these two conclusions to supply the required kernel for `ν` and `Φ`.
That published proof handles the positive finite Haar ratio, the reflected
cutoff, and the inverse dimension-th power of the ratio.

Both generic dependencies cover every natural dimension. Thus this
assembly also covers `d = 0`, when the product measure is unit point mass
and the Haar scaling factor has zeroth power one.

## Provenance

This is an internal assembly of the three published proofs above and
the existing topology certificates. It introduces no separate literature
claim; the original Fourier conventions and motivation remain documented
in the target and dependency Markdown. It assumes no local-factor,
adjacent-span, or functional-equation result. The target pair and all
existing imported pairs are preserved.
