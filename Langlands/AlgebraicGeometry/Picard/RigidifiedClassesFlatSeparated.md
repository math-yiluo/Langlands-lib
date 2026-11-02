# Conditional faithfully flat separation of rigidified classes

Assume the explicit module-level proposition
`Langlands.Scheme.Modules.LineBundleIsoDescentStatement` and uniqueness of all
relative rigidified isomorphisms. The actual rigidified class presheaf is
separated for any slice morphism whose underlying map is quasi-compact, flat
and surjective.

The generic comparison lemmas first show that compatibility of a module map
with the canonical descent comparisons is preserved by precomposition.
Consequently it suffices to check compatibility on the two projections of the
actual fibre product. For a rigidified isomorphism this overlap compatibility
is the published general relative uniqueness argument.

`descendedCarrierIso` applies the assumed module descent statement to the
underlying isomorphism, using the Cartesian relative projection square to
transfer the three hypotheses. The class-level result uses quotient
exactness, this ordinary isomorphism, and injectivity of forgetting
rigidification. It therefore does not require a new verification of
compatibility of the descended isomorphism with the rigidifications.

This is internal derived content conditional on the two stated inputs.
It does not prove module descent, effective descent of objects, or the final
fppf comparison.
