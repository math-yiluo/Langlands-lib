# Scalar Fourier closure and sigma-finiteness from self-duality

Worker 86 authored this internal prerequisite statement for the finite-row
Fourier compatibility work coordinated by Worker 110.

`Langlands.HarmonicAnalysis.ScalarFourierClosureStatement.{u}` is a closed
proposition definition. It universally quantifies over a field `F : Type u`
with `TopologicalSpace F`, `IsTopologicalRing F`, `MeasurableSpace F`,
`BorelSpace F`, `LocallyCompactSpace F`, `T2Space F`, and
`TotallyDisconnectedSpace F`, and over every
`ψ : UnitaryAdditiveCharacter F` and `μ : AdditiveHaarMeasure F`.
Its hypothesis is exactly `IsSelfDual ψ μ`. Its conclusion is the conjunction
of:

1. `MeasureTheory.SigmaFinite μ.measure`;
2. for every `f : SchwartzBruhat F`, there exists
   `g : SchwartzBruhat F` such that
   `g y = fourierIntegral ψ μ f y` for every `y : F`.

Both conclusions belong to the proposition. In particular, sigma-finiteness
is a conclusion to be proved, not an additional instance assumption.
No topological division-ring structure, valuation, chosen lattice, second
countability, nondiscreteness, or p-adic structure is required. Discrete fields
are included in the quantified scope.

The character, Haar measure, test space, Fourier integral, and self-duality
predicate are imported unchanged from
[`Langlands.HarmonicAnalysis.Basic`](Basic.md).
The character is already continuous, nontrivial, and unit-circle-valued;
the supplied additive Haar measure is regular. The integral uses the
plus-sign kernel `ψ.complex (x * y)` without conjugation. Self-duality already
requires convergence of the second integral and Fourier squared equal to
reflection. The new conclusion asserts that the first transform has an
actual compactly supported locally constant representative.

This is an internal statement extracted for the proof of
`RowFourierCompatibilityStatement` in
[`Langlands.HarmonicAnalysis.RowFourier`](RowFourier.md).
Scalar closure supplies the scalar test-function preservation obligation.
Sigma-finiteness supplies the measure hypothesis used by finite-product
integration and the existing `rowFourierTransform` construction. Neither
conclusion is claimed to follow by unfolding `IsSelfDual`, and `Basic`
does not already establish Fourier closure.

The Fourier conventions and their original-source provenance remain those
documented in `Basic.md` and `RowFourier.md`. The present proposition is an
internal prerequisite formulated in terms of their published objects, not a
transcription of a new literature theorem. It introduces no new measure,
transform, or test-function construction, and supplies no proof. A future
proof must derive both conclusions under the displayed assumptions, including
the discrete case.
