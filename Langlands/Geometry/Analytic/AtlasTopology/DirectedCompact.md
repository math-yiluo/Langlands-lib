# Compact containment in directed quasinets

Author: Worker 36.

This module derives elementary consequences of the quasinet condition for a
family `U : ι → Set X` directed by inclusion, with `Nonempty ι`. The ambient
space has its given topology. No separation hypothesis or compactness of the
members `U i` is assumed.

The source for the quasinet convention is Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), section 1.1, printed pages 13–14
(PDF pages 10–11), especially the definition before Lemma 1.1.1. The registered
source is `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The directed conclusions below are derived results, rather than assertions
stated in that passage.

`exists_sUnion_subset_of_finite` proves that the union of any finite family
of members from `Set.range U` is contained in a single `U i`. The proof
inducts on the finite family. Nonemptiness supplies an index for the empty
family. For an inserted member, directedness provides a common upper member
for it and the inductive upper member. This lemma does not use topology.

For `IsQuasinet (Set.range U)`, the finite neighborhood union at a point
therefore lies in some `U i`. Upward closure of the neighborhood filter
shows that this original member is a neighborhood of that point.
`exists_mem_nhds_of_directed` expresses this conclusion;
`exists_mem_interior_of_directed` translates it to membership in an
interior. Thus the interiors of the original members cover all of `X`.

`exists_subset_interior_of_isCompact` proves
`∃ i, S ⊆ interior (U i)` for every compact subset `S`. Interiors preserve
inclusions, so they form a directed open cover. Mathlib's
`IsCompact.elim_directed_cover` then supplies one member containing `S`.
`exists_subset_of_isCompact` follows by inclusion of each interior in
its underlying set.

The nonempty-index assumption is retained even when `X` or `S` is empty:
the conclusions require an actual index. The results neither add members
to the family nor change the ambient topology.
