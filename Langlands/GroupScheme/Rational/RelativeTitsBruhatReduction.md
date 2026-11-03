# Bruhat consequences for the actual relative Tits data

This internal supporting unit derives the kernel and ambient-group generation
clauses needed for `RelativeTitsSystemStatement`. It uses the published rational
Bruhat predicate as an explicit premise and does not prove that predicate or the
full Tits-system target. Its constructions use the existing categorical rational
points, whole-torus centralizer, normalizer, and relative Weyl quotient.

`relativeTitsCell i ν w` is the published `TitsSystem.cell` specialized to
`B = standardParabolicPoints i ν ∅` and the quotient map from the actual
normalizer onto `relativeWeylGroup i`. It includes all representatives of `w`.

The kernel of that quotient map lies in `B` because the whole-torus centralizer
lies in every standard Levi and hence every standard parabolic. Conversely, a
normalizing point in `B` belongs to the dynamic parabolic of `ν`, by the
unconditional inclusion `standardParabolic_empty_le`. It therefore belongs to
the double coset of the identity. The separation clause of
`HasRationalBruhatDecomposition` makes its Weyl class the identity. This proves
the kernel equality and `B ∩ N(k) = Z(k)`, without assuming the full minimal
endpoint equality.

For generation and cell covering, the equality of `B` with the dynamic parabolic
is an explicit additional premise. Bruhat covering expresses every rational
point as `p * n * q`. Its three factors lie in the join of `B` and `N(k)`, giving
the generation clause, and that expression supplies membership in the cell of
the class of `n`.

For disjointness, two expressions `g = p n q = p' n' q'` give
`n' = (p'⁻¹ p) n (q q'⁻¹)`. All four parabolic factors lie in the dynamic
parabolic by its one-sided endpoint inclusion. Bruhat separation identifies the
two Weyl classes. Thus disjointness needs no full endpoint equality.

These are derived group-theoretic consequences of published definitions and
predicates. No full standard-parabolic point theorem, Tits-standard-parabolic
comparison, rank-one multiplication rule, or nondegeneracy assertion is used.
The structural Bruhat and endpoint proofs remain separate obligations.
