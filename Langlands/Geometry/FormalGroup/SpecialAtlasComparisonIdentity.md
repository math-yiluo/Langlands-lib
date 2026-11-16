# Actual diagonal comparisons through special-atlas quotient reduction

This internal module shows that a specified special-atlas comparison
which is an actual identity on one refinement retains this property
under equal-scalar transport, supplied-target coefficient extension
and actual principal-quotient reduction.

It retains the local field, central division algebra and supplied
embedded subfield assumptions of special atlases. The coefficient
rings are arbitrary commutative algebras with the given structures.
The reduction result uses the existing actual `Nilp` object. Covers
may be infinite; the conclusion is existence of the one actual
refinement on which the resulting specified formal map is identity.

The transport proof eliminates equality of the scalar algebra
structures. The supplied-target proof applies that transport to the
actual `IsDiagonal.baseChange` identity. Reduction specializes this
construction to the actual quotient algebra map. These proofs do not
identify the resulting refinement with the canonical reflexive one.

The provenance is internal from `AtlasOrderComparisonIdentity` and
the existing special-atlas coefficient-extension and reduction
definitions. The resulting comparison data, including the identity
coordinate isomorphism, are retained. No point-functor equivalence or
representability assertion is substituted.
