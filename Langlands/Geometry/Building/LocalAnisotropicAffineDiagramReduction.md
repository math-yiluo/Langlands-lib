# Conditional reduction of the local anisotropic affine-diagram target

The theorem
`Langlands.Geometry.Building.localAnisotropicAffineDiagram_of_building_inputs`
proves the published proposition
`Langlands.GroupScheme.LocalAnisotropicAffineDiagramStatement` under five explicit
statement hypotheses:

- `SpecialTorusExistenceStatement`;
- `QuasiSplitDerivativeAffineRootsStatement`;
- `QuasiSplitIndivisibleDerivativeLiftsStatement`;
- `UnramifiedSpecialApartmentChamberStatement`;
- `RelativeRootSystemIrreducibleStatement`.

Every hypothesis is at the same arbitrary universe `u` as the host proposition.
The conclusion retains all of the host's field and group hypotheses, every
characteristic, the actual supplied Tits index, and its absolute Cartan block.
The theorem does not supply proofs of the five hypotheses. In particular, it
does not prove the unconditional host target.

The noncomputable definition
`localAnisotropicAffineDiagramMatrixOfBuildingInputs` chooses the resulting
integer matrix on `Option d.Vertex`, with the five supporting statements and
the host data as arguments. Its specification gives the absolute Cartan block,
diagonal entries two, nonpositive off-diagonal entries, symmetric zero pattern,
a positive integral left kernel vector, and transitivity of the group of
entry-preserving permutations.

The proof starts with a maximal split torus over the local base field `F`.
Special-torus existence supplies a closed commutative subgroup `T` containing it,
whose scalar extension to the actual field `K = inertiaFixedField F` is maximal
split. Absolute almost-simplicity ascends to `K` by
`IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`. The published
`MaximalUnramified.isQuasiSplit` gives quasi-splitness, and
`quasiSplitIntegerApartmentExistence` supplies compatible apartment and
centralizer data on exactly this scalar-extended torus. Full V6 gives coefficient stability through
`MaximalUnramified.galoisStable_of_isOmegaCompatible`, and the published
`MaximalUnramified.exists_order_eq_one` supplies the unit needed for the affine
root-system axioms.

Before any splitting or absolute maximality is known, the full derivative
statement identifies every ordinary affine derivative with the full set of
actual relative-root forms. The proved helper
`IsQuasiSplit.relativeRoots_nonempty_of_isAbsolutelyAlmostSimple` supplies an
actual relative root at this stage. Relative-root irreducibility, transferred
by `nonempty_and_isIrreducibleRoots_of_isAlmostSimple`, makes the apartment's
ordinary affine roots nonempty and irreducible.

The special-apartment chamber statement gives a regular point whose entire
ordinary sign facet is coefficient-stable inside this prescribed apartment.
The helper `exists_affineDiagramMatrix_of_quasiSplit_apartment` assembles the
remaining argument over an arbitrary Galois extension inside the separable
closure, on supplied apartment data, before specializing to this local field.
It packages those data into `IntegerValuationBuildingData`.
`KPApartmentData.chamberTransitivity_of_isAnisotropic` now gives transitivity
both on its simple affine roots and on its chamber Cartan matrix. Together with
the indivisible-lift statement, transitivity yields symmetry of the pairing
on the full derivative set through
`hasSymmetricDerivativePairing_of_transitive_simpleRoots`. The theorem
`hasReducedSimplyLacedRelativeRootSystem_of_derivative_symmetry` constructs a
reduced simply-laced root pairing on the span of all actual relative roots.
These symmetry and splitting steps are collected in
`isMaximalTorus_of_transitive_quasiSplit_derivatives`, which works with an
arbitrary affine root system on a torsor under the actual reduced translation
space and retains the full derivative equality.

The already proved conditional reduction
`quasiSplitSimplyLacedSplitting_of_relativeRootSystemIrreducible` then supplies
absolute maximality of the chosen split torus from the same relative-root
irreducibility hypothesis. There is consequently no sixth independent splitting
premise. Only after this step does the proof use
`exists_transitive_titsIndexCartanExtension_of_integerValuation`, which compares
the relative finite Cartan block with the supplied absolute Tits-index matrix.
The previously obtained regularity, nonemptiness, irreducibility and both
transitivity facts discharge the endpoint's chamber inputs.

This module is an internal composition of imported results. It transcribes no
new assertion from the literature. The mathematical source comparisons and
remaining construction obligations are those documented in the five supporting
statement modules and in the imported irreducibility and anisotropic chamber
modules. The reduction uses no local type-A classification, local rank-one
classification, or local Kneser–Tits result.
