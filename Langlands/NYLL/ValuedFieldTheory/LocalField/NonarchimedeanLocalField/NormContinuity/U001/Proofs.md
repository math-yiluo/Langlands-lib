# Continuity of the finite-dimensional algebra norm

Worker 126 supplies the exact proof increment M255.001 for
`Langlands.NYLL.LocalFieldTheory.algebraNorm_continuous_of_finiteDimensionalStatement`.
The theorem retains the source name under `Langlands.NYLL.LocalFieldTheory`:

```lean
theorem algebraNorm_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    algebraNorm_continuous_of_finiteDimensionalStatement K L
```

The target unfolds to `Continuous (Algebra.norm K : L → K)`. The universes
`u` and `v` are independent, and all source parameters and instances keep their
original order. The normed-field structures supply the topologies. The proof
uses completeness of `K`, finite dimensionality and the supplied continuous
scalar action; it adds no hypothesis or global instance.

## Implemented proof and dependencies

The proof imports the published target module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.Statements`
and the existing Library module
`Langlands.Representation.Plancherel.TorusNormKernel.FieldNormCompact`.
The target and its dependencies are unchanged.

Mathlib's `isModuleTopologyOfFiniteDimensional` supplies a local instance
`IsModuleTopology K L`: a finite-dimensional Hausdorff topological vector
space over a complete nontrivially normed field carries the module topology.
Here the normed-field structure on `L` supplies its Hausdorff topological
additive group, `Algebra K L` supplies the module structure, and
`ContinuousSMul K L` supplies continuity of scalar multiplication.

The existing theorem
`Langlands.Plancherel.TorusNormKernel.continuous_algebraNorm` then gives the
desired continuity. Its actual hypotheses are a nontrivially normed field
`K`, a field `L`, an algebra structure, finite dimensionality, a topology on
`L` and `IsModuleTopology K L`. The subsequent `ProperSpace` hypothesis in
that module belongs to its compactness results and is absent from the
continuity theorem.

That Library theorem, authored by Worker 1505, implements the determinant
argument: choose `Module.finBasis K L`, write the algebra norm as the
determinant of `Algebra.leftMulMatrix` using `Algebra.norm_eq_matrix_det`,
prove continuity of every matrix entry as a linear functional with
`IsModuleTopology.continuous_of_linearMap`, and apply
`Continuous.matrix_det`. This focused proof reuses it by Lean import.

## Source correspondence and attribution

The original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean`,
lines 32–47 (M255.001). The source file SHA-256 is
`8cd7c49384a442469cff5bf0397150f52b24b03fa3087b3b252b29e9e05b38a8`.
It is retained under
`literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source erratum was found in the available project notes.

The source proof chooses `Module.Free.chooseBasis K L`, rewrites the norm as
a determinant, proves continuity of the entire left-multiplication matrix
using `LinearMap.continuous_of_finiteDimensional`, and applies determinant
continuity. Worker 126 replaces that body with the module-topology argument
above, changes the imports to the two published modules, prefixes the
namespace, and uses the already published proposition as the theorem's
result type. This is a derived implementation of the same source result,
with the exact original parameters and independent universes. The new
modification notice records these changes.

The original copyright and author header is preserved verbatim. The
Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain at
`licenses/NYLL/`; their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.
