# Rational points and scheme-theoretic fixedness

Worker 1351.

This internal derived construction supports the exact solvable proper
fixed-point proof. It constructs `SchemeAction.orbitMap` for any group scheme
over any base, using the published actual action and the canonical map to
the terminal relative scheme. It changes no existing definition.
`comp_orbitMap` proves its evaluation formula on every relative scheme.
`isFixed_iff_orbitMap_eq` identifies all-test fixedness of a rational section
with constancy of this actual morphism. Its converse precomposes the
constancy equation with an arbitrary group point and uses uniqueness of maps
to the terminal relative scheme, so every test refinement is retained.

Over an algebraically closed field in an arbitrary universe,
`nonempty_rationalPoints` obtains a rational section of any underlying-nonempty
scheme locally of finite type. Such a scheme is Jacobson. The nonempty
intersection of its whole space with its closed points supplies a closed
point, and Mathlib's `pointOfClosedPoint` supplies the rational section.
Reducedness, smoothness and properness are unnecessary for this lemma.

`hom_ext_rationalPoints` proves that maps over the field from a reduced
locally finite type scheme to a separated scheme agree when their
precompositions with all rational points agree. Closed points are dense,
their residue fields identify with the base field, and the resulting
equalities of residue-field maps give equality of scheme morphisms by
Mathlib's separated-target extensionality theorem.

Finally, `SchemeAction.isFixed_iff_rationalPoints` assumes that the acting
group is smooth and the target scheme is separated. The published
`SmoothReducedProof.isReduced_of_smooth_over_field` gives reducedness of the
acting group. Rational invariance identifies its orbit morphism with the
constant morphism by `hom_ext_rationalPoints`. The orbit criterion then
gives all-test fixedness. The target scheme may be nonreduced. This proves a
criterion for a supplied rational point; it does not prove existence of a
fixed point or construct a closed orbit.

The derivation uses the published `SchemeAction` API, Mathlib's algebraically
closed field and separated-morphism lemmas, and the published smooth
reducedness proof. The residue-field extensionality argument generalizes the
published `Gm.hom_ext_kpoints` argument to any reduced locally finite type
source; it introduces no group-specific geometric premise or new axiom.
