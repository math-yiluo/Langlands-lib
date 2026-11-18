# The actual irreducible matrix representation of a split norm-one group

This internal construction composes the actual splitting isomorphism
`SL_1(A)_L ≅ SL_n` with the actual inclusion `SL_n → GL_n`, where
`n = reducedDegree k A`. The representation is an actual group-scheme
morphism. `representation_pointMatrix` and
`representation_pointMatrix_val` give its exact matrix over every
relative scheme test: it is the extended splitting chart evaluated on
the original tensor-algebra unit. Thus the convention is multiplication
on column vectors using the original algebra chart.

`SpecialLinear.inclusion_isIrreducible` proves irreducibility over any
field. A subspace stable on all affine tests is stable under each
determinant-one matrix over the field, by using that affine point and the
identity linear coefficient functional. The published
`eq_top_of_forall_SL_mulVec_mem` then proves that every nonzero stable
subspace is the whole vector space. Its transvection argument also
covers the one-dimensional coordinate case.

`MatrixRepresentation.IsIrreducible.restrict_iso` transports this
all-test irreducibility along an actual group-scheme isomorphism, by
pulling affine points back along its inverse. Applied to the splitting
isomorphism, this proves `representation_isIrreducible` for the actual
norm-one representation.

`canonicalRepresentation` and its irreducibility theorem use the
published unconditional finite Galois splitting chart of every central
simple algebra. The construction works with `k` and `A` in `Type u` for
every `u`, over every field and in every characteristic. It imposes no
perfection, centre-smoothness or independently supplied descent premise.

Provenance is internal: this is composition of published actual
group-scheme morphisms and a deduction from the published elementary
standard-module irreducibility lemma. It supplies the concrete
irreducible representation for the norm-one Tits comparison. Recognition
of its highest weight, comparison to the general Tits algebra and the
Brauer-class normalization are separate obligations.

The all-test restriction lemma `IsIrreducible.restrict_iso` is shared with the Tits algebra transport module through `MatrixRepresentation/IrreducibleRestriction`.
