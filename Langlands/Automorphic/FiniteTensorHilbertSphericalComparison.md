# Whole scalar spectra and full-slice spherical comparison

Author: Worker 2.

This is an internal derivation from the actual joint eigenspaces,
fixed-vector equivalences, integrated corner actions and canonical p-adic
objects. It asserts no new identification with original literature.

## Whole scalar spectra

`HasScalarSpectrum T c` requires that the carrier be nontrivial and every
operator act on every vector by its specified scalar. The joint eigenspace
equals the whole space exactly when all these equations hold; nontriviality
remains an additional requirement. An intertwining linear equivalence
transports the whole relation, including nontriviality, across independently
sized complex vector spaces.

`hasScalarSpectrum_equiv_iff` transports nontriviality by the underlying
equivalence, and transports the equations by injectivity in one direction and
surjectivity in the other. Linearity preserves the scalar multiples.
`jointEigenspace_eq_top_iff` uses the proved all-equations membership criterion
and the order characterization of the top submodule.

`hasScalarSpectrum_corner_iff` applies the existing actual fixed-space
equivalence and its proved intertwining law. It compares all vectors of a full
invariant subspace's compact-open fixed space with the fixed space of a smooth
representation genuinely equivalent to the ambient smooth intersection.
The Haar measure and compact open subgroup remain specified genuine data.
No commutation hypothesis or existence of eigenvalues or nonzero eigenvectors
is imposed.

## Canonical p-adic object comparison

The generic `TensorHilbertSphericalAux` constructions use an existing
`Correspondence.AutomorphicObject A` over a canonical p-adic field `L` and a
genuine representation equivalence from its action to the ambient smooth
intersection of an invariant subspace `S`. The coefficient field is complex;
field, original-object carrier and ambient-vector universes are independent.

`objectStandardHeckeOperator_intertwine` specializes the proved corner-action
intertwining law to the actual `Unramified.standardHeckeOperator` and
`standardHeckeElement`. The fixed-space equivalence is the existing
`factorFixedEquiv`. `objectSphericalEigenspaceEquiv` restricts this equivalence
to the actual joint eigenspaces for the existing `standardHeckeScalar`.
Its source is explicitly the ordinary joint eigenspace of the bundled object's
standard operators; its target uses the operators on the whole fixed space
of `S`.

`objectHasSpectrum_iff` applies the whole scalar-spectrum transport and the
equivalence between nontriviality of a submodule and its inequality to bottom.
It therefore compares precisely the existing
`Unramified.HasSphericalHeckeSpectrum`, which requires nonzero fixed vectors
and the equations on every vector. All constructions retain the existing
mass-one spherical Haar, integral compact open subgroup, standard diagonal
double cosets and positive square-root residue-cardinality normalization.

## Actual completed tensor slices

`HasHilbertSphericalSpectrum` applies the generic whole scalar predicate to
`sliceHilbertStandardHeckeOperator` on every spherical fixed vector of the
actual full closed tensor slice inside the supplied global Hilbert
completion. Its definition permits zero tails and requires neither
irreducibility nor admissibility. It does not assert that this predicate holds.
The generic top-eigenspace criterion applies to exactly
`sliceHilbertSphericalEigenspace`.

`sliceHilbertPadicSphericalEigenspaceEquiv` identifies the actual canonical
`sliceHilbertPadicObject` joint eigenspace with that of the full closed slice.
`sliceHilbertPadicObject_hasHilbertSpectrum_iff` compares its existing
whole-fixed-space spectrum relation with `HasHilbertSphericalSpectrum`.
Both directly specialize the generic constructions using the actual
`sliceHilbertRange` and `sliceHilbertCanonicalSmoothEquiv`. The canonical
smooth equivalence preserves the ambient vectors. The bundled object's
carrier and action are the same intrinsic smooth slice; its additional
property proofs retain the explicit nonzero complementary tensor, original
factor algebraic irreducibility and original factor admissibility in the
completion topology. No global nonzeroness premise is needed for these two
comparisons.

`UnramifiedData.hasHilbertSpectrum` transfers supplied actual unramified data
to all full closed-slice spherical fixed vectors, at every place outside its
exceptional set and for every supplied nonzero tail. It first uses the
published smooth-object spectrum theorem, then the new full-slice comparison.
The data's global nonzeroness premise and original eigenvalues are preserved.

The number field is arbitrary in universe `uF`; original local factor
carriers lie in independent universe `uV`. Every positive rank is written
`r + 1`. The presentation and invariant positive form are supplied genuine
data. This construction supplies no such form, tensor presentation,
unramified data, automorphic occurrence, spectral decomposition, eigenvalue
classification or local Langlands correspondence.
