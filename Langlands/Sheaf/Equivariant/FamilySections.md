# Indexed coefficient families on transport opens

Author: Worker 865.

`Langlands.Cohomology.CompactSoft.FamilySections A U` is the dependent product
`∀ (g : G) (y : {y : X // g • y ∈ U.openSet}), A y.1`.
Here `R`, `G`, and `X` share an arbitrary universe, `R` is a commutative ring,
`G` is a group acting on the topological space `X`, and `A` is a family of
`R`-modules. The abbreviation needs no topology on `G` or continuity of the action.

This is the unchanged definition formerly in
`Langlands.Cohomology.CompactSoft.FamilyCutoff`, moved here so both the cutoff
construction and the generic coinduced family sheaf use the same type.
Its historical namespace is retained. It is elementary supporting
infrastructure, with no sheaf condition or compactness assertion.
