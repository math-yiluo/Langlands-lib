# Actual inversion of coefficient-extended formal comparisons

This internal module proves that coefficient extension commutes with
reversal of an actual full-order formal comparison. The two original
atlases may have different, possibly infinite principal covers and
different finite coordinate types. The scalar and coefficient rings
are arbitrary commutative rings with the given algebra structure, and
the acting order is any algebra ring. Coefficient tests use the
coefficient-ring universe.

The supporting `Iso.inv_unique` and `Iso.ext_hom` use the actual formal
inverse equations and composition laws. They show that the forward
formal map determines the entire same-cover full-order isomorphism.
The isomorphism identities for reversing a composite, associativity
and coefficient extension therefore concern actual formal maps.

`Comparison.baseChange_symm` preserves the two specified refinements,
with their roles exchanged. The extended coordinate isomorphism is
the conjugate of the extended original coordinate isomorphism by
the two actual refinement/base-change identifications. Reversing this
conjugate agrees with the conjugate of the reversed map, by the
isomorphism identities and associativity.

The provenance is internal from `AtlasOrderMorphism`,
`AtlasOrderBaseChangeMorphism` and `AtlasOrderComparisonBaseChange`.
There is no replacement of a formal isomorphism by an arbitrary
equivalence of point functors, and no claim of comparison composition
coherence, descent or representability.
