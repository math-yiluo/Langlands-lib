# Cohomology composition for actual sections cochain maps

This internal construction takes homology of the actual sections maps in
`PushforwardSectionsComposition`. It uses the exact homology comparison
for restriction of scalars from `DerivedComparison` and its composition
law from `DerivedExactComposition`. All schemes, rings and modules have an
arbitrary common universe.

For a commuting square over an affine base and an actual cochain map
`t : K → h_* L`, `resolutionCohomologyBaseChangeMap` first takes homology
of `resolutionSectionsBaseChangeMap t`, then applies the exact homology
comparison for restriction of scalars. The complexes are arbitrary
nonnegative cochain complexes. They need not be resolutions, and no
geometric or acyclicity hypothesis is imposed.

`restrictScalars_mapHomologyIso_comp` identifies the homology comparison
for restriction along a composite ring homomorphism with the two successive
comparisons, retaining the canonical scalar-composition isomorphism. Its
proof uses naturality of homology under that natural isomorphism and the
composition law for exact functors on short complexes.

`resolutionCohomologyBaseChangeMap_comp` states the corresponding composition
law for actual maps `t : K → h_* L` and `s : L → j_* P`. The composite
cochain map includes the canonical identification of successive pushforwards
with pushforward along `j ≫ h`. The proof applies homology to the sections
composition identity, uses the scalar-comparison identity, and then uses
naturality of the exact homology comparison.

This result concerns homology of the specified complexes. It does not yet
assert composition of the canonical derived cohomology maps, residue tensor
naturality, or existence of a Picard-stack atlas.
