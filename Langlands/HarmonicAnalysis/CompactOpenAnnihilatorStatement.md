# Compactness of compact-open annihilators from scalar self-duality

`Langlands.HarmonicAnalysis.CompactOpenAnnihilatorStatement.{u}` is a closed
`Prop`-valued definition. It quantifies over every `F : Type u` with
`Field F`, `TopologicalSpace F`, `IsTopologicalRing F`, `MeasurableSpace F`,
`BorelSpace F`, `LocallyCompactSpace F`, `T2Space F`, and
`TotallyDisconnectedSpace F`, and over every
`ψ : UnitaryAdditiveCharacter F` and `μ : AdditiveHaarMeasure F`.
These are exactly the field, topology, character, and measure hypotheses of
[`ScalarFourierClosureStatement`](ScalarFourierClosureStatement.md).

Under `IsSelfDual ψ μ`, the proposition requires that every
`H : OpenAddSubgroup F` satisfying `IsCompact (H : Set F)` has compact
annihilator. The annihilator is the following actual subset of `F`:

```lean
{y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1}
```

The kernel uses the order `x * y` and the complex value `1`, consistently with
the plus-sign Fourier integral in [`Basic`](Basic.md).
The existing character type already requires continuity, nontriviality, and
unit-circle values. The supplied additive Haar measure is regular, as required
by its existing type. `OpenAddSubgroup` is Mathlib's open additive subgroup;
this module introduces no new character, measure, subgroup, or annihilator
data type.

There is no sigma-finiteness, second countability, continuous inversion,
valuation, nondiscreteness, or p-adic assumption. The statement preserves
the universe `u` and includes discrete fields in its quantified scope.
Compactness of `H` is an explicit hypothesis, and compactness of its
annihilator is the conclusion to be proved.

This is an internal prerequisite extracted from Worker 86's scalar Fourier
closure proof task. Its intended use is to control the support of the
Fourier transform of a compactly supported locally constant function.
It is not a claim that `Basic` already proves annihilator compactness, nor
does it assume the full scalar Fourier closure statement or a separate
sigma-finiteness theorem. The module supplies the proposition only;
establishing it requires a separate proof.

The provenance is the existing `Basic` Fourier and self-duality interfaces
and the internal decomposition of `ScalarFourierClosureStatement`, rather
than a transcription of an additional literature theorem. The underlying
Fourier conventions retain the source provenance documented in `Basic.md`.
Worker 457 authored this statement pair; Worker 86 supplied the parent
interface and the extraction of this compactness prerequisite.
