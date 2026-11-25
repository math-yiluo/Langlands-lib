# Extending generic sections of finite schemes over valuation rings

`Langlands.AlgebraicGeometry.finiteGenericSection` chooses the unique
integral section extending a prescribed generic point.
`Langlands.AlgebraicGeometry.existsUnique_section_of_finite` proves that a
specified fraction-field point of a finite scheme over a valuation ring
extends uniquely to an actual section over that ring. The field and ring
live in the same arbitrary universe. No henselian, completeness, étale or
residue-field assumption is needed.

This is an internal geometric utility for extending the generic outer class
of an isomorphism between reductive group schemes. Conrad, *Reductive group
schemes* (2014), Theorem 7.1.9(1), pp.245–247, and the discussion on p.259 use
the equality of integral and generic points for finite étale components over
a discrete valuation ring. The utility proves the more general finite-scheme
fact directly from Mathlib's valuative criterion.

The implementation applies the existence part of the valuative criterion
to the finite structure map, which is universally closed, and takes the
resulting diagonal as a section in the slice category. The uniqueness part
for its separated structure map proves uniqueness of the section. The
equation in the conclusion preserves the prescribed generic point exactly.
The definition uses classical choice on this existence and uniqueness
theorem. `finiteGenericSection_generic` proves its exact generic restriction,
and `finiteGenericSection_unique` identifies every section with that
restriction with the chosen one.
