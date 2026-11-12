# Relative cube criteria reduced to the field cube theorem

Author: Worker 2057.

This derived helper module specializes published Library results. It proves
three implications in every universe `u`:

```lean
Langlands.AbelianScheme.relativeCubeTriviality_of_fieldCubeTriviality :
  Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement.{u} →
    Langlands.AbelianScheme.RelativeCubeTrivialityStatement.{u}

Langlands.AbelianScheme.relativeRigidifiedCube_of_relativeCubeTriviality :
  Langlands.AbelianScheme.RelativeCubeTrivialityStatement.{u} →
    Langlands.AbelianScheme.RelativeRigidifiedCubeStatement.{u}

Langlands.AbelianScheme.relativeRigidifiedCube_of_fieldCubeTriviality :
  Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement.{u} →
    Langlands.AbelianScheme.RelativeRigidifiedCubeStatement.{u}
```

The field cube proposition is an explicit hypothesis. This module does not
prove that proposition or the unconditional relative cube target.

## Implemented proof

For the first implication, introduce the quasi-separated scheme `S`, abelian
schemes `A`, `B`, `C`, the actual line bundle `D` on their categorical triple
product and its three face trivializations. Apply the published theorem
`RelativeCubeAssembly.nonempty_iso_structureSheaf_of_faces` with the given
field cube hypothesis and the two published unconditional proofs
`Langlands.AlgebraicGeometry.Picard.localTwoAxisTriviality` and
`Langlands.AbelianScheme.rigidifiedClassesZariskiSeparated`.
The local two-axis proposition is definitionally the hypothesis written out
in the assembly theorem.

The assembly transports the face isomorphisms to field fibres, applies the
field cube input, obtains local trivializations from the local two-axis
theorem, and glues their rigidified classes by Zariski separatedness.
Those constructions and their proofs remain in the imported
`RelativeCubeAssembly` module.

For the second implication, introduce `S`, `A`, `B`, `C`, actual rigidified
family classes `q`, `r` and the two unit-axis equalities. Apply the published
`Langlands.AbelianScheme.rigidifiedClasses_eq_of_ordinaryCubeTriviality`
with `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` and the
ordinary relative criterion specialized to `S`, `A`, `B`, `C`. The adapter
forms the ordinary difference bundle, transports its face trivializations,
and corrects the resulting isomorphism to respect rigidification.

The third implication composes the first two. All three statements retain
the arbitrary universe. They use the actual module-sheaf isomorphisms,
chosen relative products, rigidified quotient and pullbacks of the
published statements. They impose no additional restriction on the bases,
parameters or line-bundle classes.

## Derived provenance

These implications are internal compositions of the published results
named above; they introduce no independent geometric assertion or external
source translation. The geometry and original-source comparisons are
documented in the paired Markdown of `RelativeCubeAssembly`,
`LocalTwoAxisTrivialityProof`, `RigidifiedClassesZariskiSeparatedProof`,
`PullbackTensorProof` and `RelativeCubeDualComparison`. The module preserves
those pairs and both relative statement pairs.
