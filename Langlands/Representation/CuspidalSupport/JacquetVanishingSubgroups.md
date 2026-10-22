# Subgroup comparisons for Jacquet vanishing

Author: Worker 169.

These internal algebraic lemmas compare the actual subgroups in the published
geometric-piece construction. They hold over every field, in every rank,
including zero. They neither assert the geometric lemma nor prove either
positive-rank vanishing target. Their role is to supply the subgroup dichotomy
in the eventual proof of BZ77 2.13(a),(b).

`block_indices_subsingleton_of_parabolic_eq_top` shows that a full standard
block parabolic has at most one block. If two blocks have distinct indices,
order them and swap one coordinate from each block. The corresponding
permutation matrix belongs to the full parabolic, but has a unit entry below
the block diagonal, contradicting the defining zero condition.

`leviSubgroup_eq_top_of_parabolic_eq_top` then writes every ambient matrix as
the embedded Levi projection. After expressing its coordinates through the
block-index equivalence, the subsingleton block-index type reduces all entries
to the same-block formula for that embedding.
`refinedLevi_eq_top_of_refinedParabolic_eq_top` applies this result to each
factor: inserting an arbitrary matrix in one coordinate of the product Levi
shows that the corresponding constituent parabolic is full.

`conjugatedLevi_eq_targetIntersection` uses the actual
`intersectionLeviConjugation` equivalence and its embedding equation. If the
source intersection Levi is full, its entire embedded Levi is conjugated onto
the embedded target intersection. Both subgroup inclusions are obtained from
this equivalence, using its inverse for the reverse inclusion.

`conjugatedLevi_eq_refinement_of_source_full` combines this comparison with the
two supplied `IsIntersectionRefinement` identifications and the full-parabolic
lemma. Thus a full source refinement identifies the conjugated source Levi
with the embedded target refinement. If the target refinement is full too,
`levisAssociated_of_intersection_refinements_full` uses the same permutation
to witness association of the ambient Levis.

The final two consequences preserve the distinct negative hypotheses needed
by the two vanishing targets. The absence of any associated target refinement
forces each source refinement to be proper. For merely nonassociated ambient
Levis, a full source refinement forces the target refinement to be proper.
Here “proper” means that the actual refined parabolic subgroup is not top.
The intersection identifications are explicit hypotheses of these subgroup
lemmas; their existence is left to the geometric lemma.

These proofs derive directly from existing matrix, subgroup and conjugation
definitions. They are internal supporting arguments, not a claim that the
literature contains this explicit matrix proof. No additional axioms,
representation restrictions, or existence assumptions on a geometric
filtration are introduced.
