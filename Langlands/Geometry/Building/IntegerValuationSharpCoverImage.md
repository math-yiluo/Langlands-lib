# Sharp fixers in the simply connected image over an integer-valued field

This private support draft for Task 6309 generalizes the algebraic argument in
the published `KPSharpCoverImageProof` from its local-field datum to an arbitrary
field, maximal split torus and simply connected derived cover. Its intended use
is the easy inclusion in the comparison assigned to statement Task 6479.
It does not prove the reverse inclusion or the final affine-root statement.

For an actual relative root, the published rank-one factorization constructs
reflection data. The published commutator cocharacter `derivedCocharacter` lands
in the actual derived subgroup and pairs with the root to four. Factoring this
cocharacter through the represented derived subgroup makes the entire root
subgroup contract. The published rational unipotent lifting theorem then lifts
every root-group point through the supplied simply connected derived cover.
No topology or valuation is needed for this algebraic step.

The sharp fixer is the supremum of the root fixers, each contained in its root
group. Thus every sharp fixer lies in the simply connected image. Independently,
antitonicity reduces pointwise fixing to the published singleton containment.
Over the maximal unramified field the simply connected image lies in
`E.zeroPoints` by its defining join, so the sharp fixer does too. Finally, the
zero-group fixer of the whole apartment fixes every subset. Taking the join
proves the right-to-left inclusion in the intended zero/sharp equality.

All results hold for every apartment subset, including the empty and unbounded
cases. They require no AS5, building-existence premise or extra apartment axioms.
The reverse inclusion for nonempty bounded subsets remains a separate source
and proof obligation. This is internal derived content: its provenance is the
published root-lifting proof and the definitions of the sharp and zero subgroups,
rather than a new assertion of the full source comparison.
