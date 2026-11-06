# The finite torsion subgroup determined by a commensurable lattice

Author: Worker 1730.

This is an internal construction derived from the published full Tate limit,
its rationalization and its actual geometric monodromy. No external source is
used. The input `L` is an additive subgroup of the full rational Tate module;
an integral finite-adele submodule supplies such a subgroup by forgetting scalars.

For a natural number `n`, `normalizedIntegralSubgroup` consists of full
integral families `x` for which `toRational x = n • w` for some `w ∈ L`.
For a positive full index `n`, `fullSquareIndex n` is the positive index
`n²`, and `normalizedLevelSubgroup` is the evaluation image of the normalized
integral subgroup at that index. The first constructions work for every
commutative group scheme and every test scheme.

The lower bound `n • im(T) ⊆ L` implies that the normalized integral subgroup
contains `n² • T`. A general saturation lemma, proved using the division
lemma in `FullEvaluationKernel`, shows that any subgroup containing `m • T`
is the full preimage of its image under evaluation at `m`. Applying it with
`m = n²` gives `evaluation_mem_normalizedLevelSubgroup_iff`.
The upper bound `n • L ⊆ im(T)` separately supplies an integral element of
the normalized subgroup for every element of `L`.

For an actual abelian scheme at a field-valued point, if `L` is stable under
the published rational monodromy, the normalized integral subgroup is stable
under integral monodromy. This follows from `toRational_monodromy` and the
fact that additive automorphisms commute with natural multiplication. Evaluation
intertwines integral and level monodromy, so the torsion-level subgroup is
stable under the actual level monodromy. The reverse implications use inverse
monodromy elements.

No geometric subgroup scheme or quotient is constructed here. Finiteness of
the torsion-level subgroup follows separately from the published geometric
level-finiteness theorem when its positive index is invertible and the
geometric fibres are finite; no finiteness premise is needed for the algebraic
constructions and exact preimage comparison themselves.
