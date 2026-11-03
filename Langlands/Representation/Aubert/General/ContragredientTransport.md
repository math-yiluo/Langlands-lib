# Smooth-dual compatibility with actual change of acting group

This internal module proves compatibility of the actual smooth dual with
pullback along a topological group equivalence. It applies to arbitrary
topological groups and complex smooth representations, with independent
group universes and carrier universe. It is an ingredient for associated
Levi transport; it supplies no induction or opposite-Jacquet duality.

`contragredientPullbackIso e A` identifies the smooth dual of the actual
pullback of `A` with the actual pullback of its smooth dual. It bundles the
published generic
`Langlands.CuspidalSupport.QuotientAssembly.smoothDualPullbackEquiv`.
The isomorphism preserves each underlying linear functional. Both
continuous directions of `e` identify the smooth-functional submodules;
the action compatibility follows from preservation of inverses.
`contragredientPullbackIso_hom_apply` records the unchanged functional.
`contragredientPullbackIso_natural` proves the contravariant naturality
identity by equality of the actual underlying maps: both composites
precompose the functional with the given morphism.

`contragredientK0_comp_pullback` proves commutation on the whole existing
exact finite-length Grothendieck groups. Its compact-open cofinality and
smooth-dual finite-length premises are precisely those needed to define
the two smooth-dual K0 maps. The representation comparison is proved by
the preceding isomorphism; it is not an extra compatibility hypothesis.
The proof applies `FiniteLengthGrothendieckGroup.hom_ext_object`, expands
`pullback_ofRepresentation` and `contragredientK0_ofRepresentation`, and
uses `ofObject_eq_of_iso`. Pullback preserves finite length by the
published `pullbackFunctor_preservesFiniteLength`.

`contragredientK0_comp_conjugationK0` specializes this result to the
published continuous conjugation equivalence between subgroups of an
ambient topological group. It uses the actual `conjugationK0`, with the
membership convention `x ∈ N ↔ g⁻¹ x g ∈ M`. This comparison does not
establish equality of inductions from opposite parabolics.

The provenance is internal, from the named published constructions.
The only declaration reused from
`CuspidalSupport.LeviCuspidalQuotientProof` is its general
`QuotientAssembly.smoothDualPullbackEquiv`. That definition is independent
of the product-Levi quotient theorem and uses
`isSmoothVector_dual_comp_continuousMulEquiv_iff` and `map_inv`.
The former is proved from `dual_comp_monoidHom`,
`isSmoothVector_comp_continuousMulEquiv_iff`, and smooth-vector pullback
along the continuous inverse.

The imported quotient-proof module also contains product-Levi cuspidal
quotient and admissibility results and imports natural induction
duality. None of those declarations enters this module's isomorphism or
proof bodies. This distinguishes incidental imports from actual
declaration-level dependencies. No Langlands classification, character
independence, geometric lemma, adjointness, or cuspidal-support theorem
is used in these bodies. The K0 constructions have their existing
exactness and finite-length dependencies from `AlternatingOperator` and
`FiniteLengthGrothendieckTransport`; this module does not change or
discharge the final rational target's missing duality obligations.
