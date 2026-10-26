# Sigma-finiteness from intrinsic Fourier self-duality

`Langlands.HarmonicAnalysis.SelfDualSigmaFiniteStatement.{u}` is a closed
`Prop`-valued definition. It quantifies over every `F : Type u` with, in order,
`Field F`, `TopologicalSpace F`, `IsTopologicalRing F`, `MeasurableSpace F`,
`BorelSpace F`, `LocallyCompactSpace F`, `T2Space F`, and
`TotallyDisconnectedSpace F`, and then over every
`ψ : UnitaryAdditiveCharacter F` and `μ : AdditiveHaarMeasure F`.
It states that `IsSelfDual ψ μ` implies
`MeasureTheory.SigmaFinite μ.measure`.

The character, regular additive Haar measure, and intrinsic self-duality
predicate are imported unchanged from
[`Langlands.HarmonicAnalysis.Basic`](Basic.md). In particular, self-duality
includes convergence of the second Fourier integral and the reflection
identity for compactly supported locally constant complex functions, with
the plus-sign kernel specified there.

This is the first conjunct of the conclusion of the published
[`Langlands.HarmonicAnalysis.ScalarFourierClosureStatement`](ScalarFourierClosureStatement.md),
extracted as a separate internal prerequisite for its proof. Worker 492
made this extraction from Worker 86's statement. Its provenance is that
existing internal statement and the constructions documented in `Basic.md`;
it is not a new transcription from the literature.

Sigma-finiteness is the conclusion to be proved. The statement adds no
continuity of inversion, topological division-ring structure, nondiscreteness,
countability, valuation, scalar Fourier closure, or sigma-finiteness premise.
Discrete fields remain in its scope. This module supplies the proposition
only, with no proof that self-duality implies it. A proof must establish the
entire displayed implication under exactly these hypotheses.
