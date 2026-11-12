# Continuity of the finite-dimensional field norm on units

Worker 202 supplies the exact proof increment M255.002 for the published
proposition
`Langlands.NYLL.LocalFieldTheory.normUnits_continuous_of_finiteDimensionalStatement`.
The source theorem name is retained under `Langlands.NYLL.LocalFieldTheory`,
with this complete telescope:

```lean
theorem normUnits_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    normUnits_continuous_of_finiteDimensionalStatement K L
```

The independent universes `u` and `v`, argument order and all instances are
unchanged. The target unfolds to `Continuous (normUnits K L)` for the actual
published homomorphism `normUnits K L : Lˣ →* Kˣ`. The normed-field structures
provide the field topologies, and the unit groups have Mathlib's canonical unit
topologies. No local-field, separability or Galois assumption is required.

## Implemented proof and dependencies

The module imports the published target module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.Statements`
and the published M255.001 proof module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.U001.Proofs`.

The proof first unfolds the target and `normUnits`, reducing the goal to
continuity of `Units.map (Algebra.norm K : L →* K)`. It applies Mathlib's
`Continuous.units_map` to the field norm, using the existing theorem
`Langlands.NYLL.LocalFieldTheory.algebraNorm_continuous_of_finiteDimensional K L`
for its continuity premise. That theorem's Prop-valued result unfolds to
`Continuous (Algebra.norm K : L → K)`.

`Continuous.units_map`, in `Mathlib.Topology.Algebra.Monoid`, uses
`Units.continuous_iff` to check the value and inverse-value coordinates:
both are compositions of the supplied continuous homomorphism with the
canonical continuous unit projections. Thus it proves continuity for the
actual unit topology.

The imported M255.001 proof, authored by Worker 126, installs the local instance
`IsModuleTopology K L` with `isModuleTopologyOfFiniteDimensional` and applies
`Langlands.Plancherel.TorusNormKernel.continuous_algebraNorm` from
`Langlands.Representation.Plancherel.TorusNormKernel.FieldNormCompact`.
That theorem implements the determinant-of-left-multiplication argument.
This increment reuses these published declarations by Lean name.

## Source correspondence and attribution

The original is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean`,
lines 49–58, unit M255.002,
`LocalFieldTheory.normUnits_continuous_of_finiteDimensional`.
The original source file SHA-256 is
`8cd7c49384a442469cff5bf0397150f52b24b03fa3087b3b252b29e9e05b38a8`.
It is retained under
`literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the available project errata notes.

The source proof also unfolds `normUnits` and applies `Continuous.units_map`
to `algebraNorm_continuous_of_finiteDimensional`. Worker 202 preserves that
proof route, prefixes the namespace, replaces the raw result with the already
published proposition, and adds a `change` step to unfold that proposition.
The original imports are replaced by the two focused published modules above;
the unused source scope openings and noncomputable section are omitted.
The theorem's source parameters, instances and independent universes are
retained. The new modification notice records these changes.

The original copyright and author header is preserved verbatim. The unchanged
Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain at `licenses/NYLL/`.
Their verified SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE contains no source-specific entry for this file.
