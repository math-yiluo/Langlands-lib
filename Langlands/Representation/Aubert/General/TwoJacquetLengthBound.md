# Length from two actual Jacquet modules

This internal algebraic deduction concerns an arbitrary actual smooth complex
representation `A` of a locally compact nonarchimedean group. The group and
representation carrier have independent universes. Two semidirect decompositions
may have different Levi subgroups. Each unipotent subgroup is closed and is a
limit of compact subgroups.

The assumptions are that both normalized Jacquet modules of `A` are irreducible,
and that every irreducible subquotient of `A` has a nonzero Jacquet module for
at least one of the two decompositions. No finite length of `A` is assumed.

`two_jacquet_compositionLengthAtMost_two` applies the published finite exact-family
length theorem `Langlands.exactFamilyLengthBound`. Its family is indexed by
`Bool`, with the first and second actual Levi groups as its possibly different
target groups. `jacquetFunctor_map_isShortExact` supplies exactness of each
actual normalized Jacquet functor from the compact-limit hypothesis. Each
image has length one by `repLength_eq_one_iff`; hence the sum of the two bounds
is two. The displayed irreducible-subquotient detection premise is exactly the
detector required by the finite-family theorem.

`twoJacquetCompositionSeries` chooses an actual invariant-subspace filtration
with simple successive quotients from this result. Its index lies in `Fin 3`,
so the returned filtration has zero, one, or two factors. The proof
`two_jacquet_repLength_le_two` uses the same composition series and
`repLength_eq_of_hasSimpleFactors` to bound the actual group-algebra length.
Finally, `two_jacquet_proper_subrepresentation_irreducible` applies
`SmoothRep.subrepresentation_quotient_length_eq_one` and
`repLength_eq_one_iff`: every nonzero proper invariant subspace and its actual
quotient are irreducible.

This is a derived use of published algebraic proofs, without a new literature
assertion. The finite-family proof uses existence and transitivity of actual
irreducible subquotients, exact transport of subquotients, additivity of module
length, and the bounded strict-chain criterion for a composition series. It
does not use Langlands classification, character independence, adjointness, the
geometric lemma, or a cuspidal-support theorem. Its import of a module in the
cuspidal-support namespace reuses only that module's elementary construction
of a lower invariant subspace.

For induction in the nonself-associated rank-one case, the simplicity of
the two middle Jacquet modules and their joint detection of irreducible
subquotients remain separate representation-theoretic obligations. This pair
does not prove either premise, instantiate the rational-point geometry, prove
an exponent sign or analytic criterion, or prove
`RationalRankOneSelfAssociationStatement`. The definitions and statements
of that target remain unchanged.
