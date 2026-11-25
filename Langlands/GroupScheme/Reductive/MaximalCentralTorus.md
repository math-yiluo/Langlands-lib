# Maximal central relative tori

This internal support module names the local maximal-central-torus predicate
of `ReductiveDerivedCentralIsogenyStatement` and proves the centre
factorization used in its existence clause. It imposes no reductivity
assumption and does not assert that a scheme-theoretic centre or its largest
subtorus exists.

`IsMaximalCentralRelativeTorus z` means that `z : Z ⟶ G` is closed and
central, `Z` is an étale-locally split relative torus, and the range of every
closed central relative torus is contained in its range on every test
scheme. This is a largest-subgroup property. `range_eq` proves equality of
the ranges of two such representatives by applying their containment
properties in both directions.

`isMaximalCentralRelativeTorus_comp_center` starts with a representative
`c : C ⟶ G` of the full scheme-theoretic centre and a largest closed relative
subtorus `t : Z ⟶ C`. Its composite is closed, central and a relative
torus. Every closed central torus `t' : T ⟶ G` factors through `c` by
`SubgroupFunctor.IsRepresentedBy.factorHom`. The factor is a closed
immersion because its composite with the closed immersion `c` is closed.
The largest-subtorus hypothesis factors it further through `t`. Composing
these factorizations gives containment in the range of `t ≫ c` on all
test schemes. `exists_maximalCentralRelativeTorus_of_center` packages this
calculation as an existence implication with the largest-subtorus witness
still an explicit premise.

All bases and test schemes are arbitrary in universe `u`. The centre is
the full all-test centre, including nonreduced structure. The provenance is
internal: the predicate is an exact naming of the published target's local
predicate, and the lemmas are deductions from published representation,
closed-immersion and centrality interfaces. No external structural theorem
or unproved existence statement is used.
