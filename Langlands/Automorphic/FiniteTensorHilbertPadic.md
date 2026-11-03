# Canonical p-adic objects of actual smooth Hilbert tensor slices

Author: Worker 2.

This internal construction places the actual intrinsic smooth Hilbert tensor
slice in the existing canonical p-adic correspondence category. It compares its
genuine class with the published form-space local component and transfers the
whole spherical fixed-space Hecke spectrum from supplied actual unramified data.

## Actual inputs and topology

`F : Type uF` is an arbitrary number field. Rank is positive, written `r + 1`,
and scalars are complex. Original local factor carriers lie in independent
universe `uV`; no topology is imposed on those carriers. The local group is the
actual general linear group over the completion of `F` at its finite place `v`.
The published `CompletionPadic.padicField v` uses that same field carrier.

`P` is a supplied genuine finite tensor presentation of the actual invariant
automorphic form space `S`. The form `b` is a supplied invariant positive form
on its action. The smooth range remains the actual intersection inside the
original restricted completed global action. No new range or ambient space is
substituted.

The generic `TensorPadicAux.objectOfTopologyEq` bundles a given representation
for an equal group topology. It preserves exactly the carrier and action and
rewrites the topology only in its smoothness and admissibility proof obligations.
It works for arbitrary fields, groups and independently sized carriers.
The actual application uses the published equality `localGL_topology_eq`
between the completion matrix topology and the canonical p-adic matrix topology.
The original intrinsic smoothness proof needs neither a nonzero tail nor factor
admissibility. The object's additional admissibility and irreducibility
obligations retain their explicit factor properties and nonzero tail.

## Correspondence representative and genuine class

`sliceHilbertPadicObject` bundles exactly the intrinsic smooth range carrier
and its inherited action in `Correspondence.AutomorphicObject`. Its carrier
universe is `uF`. It requires a specified nonzero complementary tensor, original
factor algebraic irreducibility including nonzeroness, and original factor
admissibility. The previously proved property transports and the topology
equality discharge the object's obligations.

`sliceHilbertPadicClass` takes the existing quotient by genuine representation
isomorphism. The comparison `sliceHilbertPadicClass_eq` uses the actual smooth
slice change equivalence and the correspondence's quotient equality criterion.
It permits different supplied global positive forms, realizations, presentations
and nonzero tails of the same fixed original tensor data.

`sliceHilbertPadicClass_eq_localComponent` compares with the existing actual
form-space component. It retains that component's global nonzeroness premise.
The actual equivalence runs from the intrinsic smooth slice back to the given
original factor and then to the form-space component. The genuine canonical
p-adic classes therefore agree.

## Sphericality and supplied Hecke spectra

`sliceHilbertPadicClass_isSpherical_iff` identifies sphericality with nonzero
fixedness of the original factor under the actual integral local subgroup.
The proof uses the existing equality between that subgroup and the canonical
spherical subgroup, the factor-to-smooth-slice equivalence, and fixed-space
invariance under equivalence. It requires no global nonzeroness premise.
Outside the exceptional set the actual reference vector is nonzero and fixed,
which proves `sliceHilbertPadicClass_isSpherical`.

`sliceHilbertPadicObject_hasSpectrum_iff` compares the existing normalized
whole-fixed-space Hecke spectrum relation on the actual completed representative
with the existing relation on the form-space component. The quotient spectrum
criterion and the proved class comparison give both implications. The global
nonzeroness premise is retained. All mass-one spherical Haar and positive
square-root residue-cardinality normalizations are inherited from the existing
Hecke operators; no eigenvalue convention is altered.

`UnramifiedData.hasSpectrum_hilbertSmooth` applies this equivalence to a supplied
`P.UnramifiedData hS T` at any place outside `T`, for any supplied nonzero tail.
It proves the entire fixed space satisfies the specified scalar equations,
including nonzeroness, using exactly the original eigenvalues. It asserts no
existence or uniqueness of these spectral data.

## Provenance and limits

This is an internal derivation from the published intrinsic smooth-slice
constructions, completion-to-canonical topology and subgroup equalities,
`PadicLocalCategory`, `PresentedUnramifiedData`, and the genuine correspondence
class and Hecke-spectrum criteria. The proof routes are described above.
No new identification with original literature is asserted.

Presentations, positive forms, nonzero tails, and factor properties remain
explicit genuine input data. The constructions give no existence of these
inputs, automorphic occurrence, factorization of arbitrary representations,
spectral decomposition, normalized local Langlands correspondence, uniqueness
across different tensor families, isometry, or equality of embedded subspaces.
