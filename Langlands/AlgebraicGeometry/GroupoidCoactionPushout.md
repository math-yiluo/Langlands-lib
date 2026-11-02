# The relation ring as a tensor square

This module combines the relation-ring invariant equivalence with
the conditional counit equivalence. Let `B` and `C` be commutative rings
in an arbitrary universe `u`, with source algebra map `s : B →+* C`
and target map `t : B →+* C` satisfying `RingEtaleEquivalenceRelation t`.
It assumes that every coaction on a `B`-module in `Type u` is
acyclic and that a subsingleton invariant module forces its underlying
module to be subsingleton. It constructs the canonical map
`B ⊗[A] B → C`, `b ⊗ b' ↦ s(b)t(b')`, for the actual equalizer ring
`A = invariantRing t`.

The target map is an `A`-algebra homomorphism because source and target
agree on `A`. The tensor lift with the source map defines the displayed
map. Base change of `relationInvariantEquiv` followed by the conditional
counit is a linear equivalence with the same pure-tensor formula.
Consequently the actual tensor ring map is bijective and is an algebra
equivalence. Transporting Mathlib's tensor pushout across this equivalence
and flipping the square gives the relation maps in target, source order.

The scalar extension of `relationInvariantEquiv` is taken from `A` to `B`;
its composite with the counit has underlying linear map equal to
`relationTensorHom t`. `AlgEquiv.ofBijective` therefore packages this very
map as `relationTensorEquiv`, with the displayed pure-tensor formula.
`isPushout_invariantRing` is an actual categorical pushout in `CommRingCat`,
whose last two maps are `t` and `s`, respectively.

This is internal infrastructure for the Serre criterion, derived from
the actual invariant ring, the previously constructed relation coaction,
the conditional counit, and Mathlib's tensor-product pushout. It translates
no new literature theorem. The imports retain the published coaction and
acyclicity definitions. It does not prove the zero-detection premise or
the final affine quotient assertion.
