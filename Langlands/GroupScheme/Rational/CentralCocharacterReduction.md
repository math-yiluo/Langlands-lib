# Central cocharacters and quasi-split solvability

This is a derived supporting construction for the finite-field central-cocharacter
solvability problem. It introduces no further assertion from the literature and
does not prove the finite-field target. All universes are arbitrary.

For any base scheme `S`, let `χ : Gm S → G` be an actual cocharacter whose dynamic
centralizer is the full subgroup functor. The proved
`Dynamic.parabolic_eq_top_of_centralizer` identifies its dynamic parabolic with
the full group functor. If a monomorphism `i : P → G` represents that parabolic,
`Dynamic.isoOfCentralParabolic` constructs an isomorphism `P ≅ G` by the existing
uniqueness of group schemes representing the same subgroup functor. The other
representation is the identity of `G`. Its forward map is exactly `i`, as proved
by `Dynamic.isoOfCentralParabolic_hom`.

Over a field, `isIso_parabolic_of_central_cocharacters` assumes the Library
proposition `ParabolicDynamicStatement`, connected reductivity, and that every
cocharacter defined over that field has full dynamic centralizer. Given any
parabolic inclusion, the comparison supplies a cocharacter whose dynamic
parabolic is its range. The inclusion is a monomorphism because it is a closed
immersion. The preceding construction therefore makes it an isomorphism.

Finally, `IsQuasiSplit.isSolvableGroupScheme_of_central_cocharacters` applies this
result to the solvable parabolic supplied by
`IsQuasiSplit.exists_solvable_parabolic`. The original geometric solvability
predicate is transported across its inverse isomorphism with
`IsSolvableGroupScheme.of_iso`.

The cocharacters throughout the field-level results are over the ground field;
there is no descent assumption for cocharacters over an algebraic closure. The
parabolic comparison remains an explicit premise of these supporting results.
Finite-field quasi-splitness, lifting through the unipotent quotient, and an
unconditional proof of the comparison are still needed for the host theorem.

The full subgroup functor is represented by the identity using the existing
`SubgroupFunctor.top_isRepresentedBy_id` from
`Dynamic/CentralizerReductiveTransport`.
