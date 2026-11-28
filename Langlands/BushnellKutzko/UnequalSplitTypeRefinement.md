# Refinement for a split type of unequal positive level

For `e₂e₁ = 0`, `blockFiltrationUnipotent` is the subgroup `M_j` of units
`1 + x` with `x ∈ P^j` and `e₁ x e₂ = x`. These subgroups decrease with
`j` and exhaust the subgroup of units `1 + x` satisfying `e₁ x e₂ = x`,
since the filtration lattices exhaust the endomorphism algebra. For
idempotent `e₁` and `e₂`, the stages are `1 + (e₁ A e₂ ∩ P^j)` and their
union is `1 + e₁ A e₂`.

`unequal_not_le_relations_blockUnipotent` takes a simple character `θ`, a
Bushnell–Kutzko additive character, and a twist `ϑ = θ ψ_c` with `e₂ce₁ = 0`.
It assumes that the `ϑ`-isotypic subspace is finite-dimensional and has a
vector outside the relations for `ker ϑ`. At sufficiently large depth, the
simple character is trivial on `M_j`, and cyclicity of trace and `e₂ce₁ = 0`
make `ψ_c` trivial there. Hence a deep `M_j` maps into `ker ϑ`. The supplied
shift and vector transfer then yield an isotypic vector outside the
relations for the union, `blockUnipotent e₁ e₂ h₂₁ ⊤`.

This is the descent of Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), printed pp. 282–289, expressed using the subspaces of Jacquet relations.
