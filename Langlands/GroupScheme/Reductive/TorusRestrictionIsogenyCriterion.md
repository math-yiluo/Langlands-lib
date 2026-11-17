# Isogenies from finite torus restrictions and equal root counts

This internal derived result supports the verification step in the affine
split Isogeny Theorem. It does not construct a homomorphism.

The defined isomorphism `imageIsoOfFiniteTorusRestrictionFinrankEq`
identifies the actual schematic-image group scheme of the specified
homomorphism `q` with its target `H`. It applies to connected reductive
field groups when the restriction to a maximal source torus factors
through a finite map into a closed target torus, and their actual Lie
dimensions agree. Its forward map is the canonical schematic-image
inclusion, as recorded by
`imageIsoOfFiniteTorusRestrictionFinrankEq_hom`. It specializes
`imageIsoOfFiniteFinrankEq` using the finite-map conclusion established
below.

Over any field `k`, `isIsogeny_of_finite_torus_restriction_of_finrank_eq`
considers connected reductive group schemes `G` and `H` and a homomorphism
`q : G ⟶ H`. Suppose its restriction to a specified maximal torus of `G`
factors through a finite homomorphism `t` to a specified closed torus in `H`.
If the actual Lie algebras of `G` and `H` have equal dimensions over `k`,
then `q` is finite, flat and surjective, hence an isogeny. The target
torus need only be closed in this first result.

The proof combines three published results. The finite torus restriction
implies finiteness of the full scheme-theoretic kernel by
`kernel_isFinite_of_finite_torus_restriction`. The smooth connected affine
finite-kernel criterion `isFinite_hom_of_finite_kernel` then makes `q`
finite. Finally `isIsogeny_of_isFinite_of_finrank_eq` gives flatness and
surjectivity from equality of the actual Lie dimensions. No smoothness
or reducedness of the kernel is assumed.

`isIsogeny_of_torus_restriction_of_root_card_eq` specializes this criterion
to specified split maximal tori and actual root data. If `t` is an
isogeny and the two finite root-index types have equal cardinality, then
`q` is an isogeny. Here `IsRootDatumOf.finrank_lie_eq_torus_add_card`
expresses each group Lie dimension as its torus Lie dimension plus its
number of roots; `Lie.finrank_kernel_eq_of_isogeny` identifies the two
torus Lie dimensions.

These are compositions of the imported Library results, rather than
new claims taken directly from the literature. Their use for the affine
Isogeny Theorem corresponds to the verification on fibres in Conrad,
*Reductive group schemes* (2014), Theorem 6.1.16(1), §6.2, and
Proposition 6.1.10. The registered source is
`conrad-2014-reductive-group-schemes`. The homomorphism construction
and passage from the global root datum to field fibres remain separate
obligations.
