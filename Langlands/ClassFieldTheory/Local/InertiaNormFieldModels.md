# Compatible presentations of finite local models

Author: Worker 60.

These internal helpers are in
`Langlands.ClassFieldTheory.Local.InertiaNormFieldModels` and are used by
`InertiaNormActualModels` to construct the actual model of a finite tower.

`fieldRange_eq_adjoin` proves the symmetry of a compositum through a compatible
embedding by induction on field generation, preserving the two scalar maps,
addition, multiplication and inverses. Neither base is required finite.
`exists_compatible_closure_map` uses algebraicity over an actual finite
intermediate field and `IsAlgClosed.lift` to embed the original algebraic
closure into that intermediate field's closure, fixing the intermediate field.
Restricting scalars gives the required compatibility over the original base.

`fieldRange_eq_inertia` combines this compositum identity with the published
`Langlands.PadicField.inertiaFixedFieldBaseChange`. The image of the original
inertia field is explicitly identified with the range of its scalar map. Its
embedding compatibility and generation hypotheses are supplied in the model
construction in `InertiaNormActualModels`.

`map_disjoint_fieldRange` transports both subalgebras through one injective
algebra homomorphism using Mathlib's preservation of linear disjointness.
`rebaseField` changes the base along a commuting field equivalence and keeps
the identical subfield of the ambient field. The finite-dimensional and Galois
properties are transported through Mathlib's two-field-equivalence results.
For disjointness, change the coefficients of a basis along the base equivalence;
the same vectors remain linearly independent over the unchanged extension.

`total_ramification_of_image_inertia` maps the finite upper field into the
actual closure, transports disjointness, and applies the published theorem
`Langlands.PadicField.inertiaDisjointTotallyRamified`. The image equivalence
transports finite dimensionality and degree. The ramification equality is for
that same image with its canonical p-adic structure.

These are derived algebraic adapters for Serre, *Local Fields* (1979), V.4,
Lemma 7 and Proposition 7, printed pages 89–90 / PDF pages 96–97, registered
`serre-1979-local-fields`. The arithmetic comes from the two named published
proofs. The original-source and applicable corrections reading record is in
`InertiaNormDescent.md`. No unpublished peer draft was reused.
