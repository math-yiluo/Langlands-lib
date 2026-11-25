# The rank-one type-D branch in ranks at least five from local components

This internal module proves conditional consequences for an actual index `d`
of a simply connected absolutely almost-simple affine group locally of
finite type over a nonarchimedean local field. The group has split rank one
and a supplied numbering of every actual Cartan entry by `D_n`. Each theorem
has the explicit universal premise
`LocalAnisotropicCartanComponentsStatement.{u}`. That premise remains
unproved here, so these theorems do not establish the unconditional local
rank-one enumeration.

`localRankOneTypeD_le_five_of_components` proves `n ≤ 5` when `n ≥ 5`.
The existing local presentation and marking theorem gives exactly
zero-based vertex `1` as the distinguished subset, with the original supplied
numbering. If `n ≥ 6`, the zero subdiagram therefore contains vertex `n-3`
and the three distinct neighbors `n-4`, `n-2`, `n-1`. Each of the three
ordered Cartan entries is `-1`, by `CartanDNumbering.eq_neg_one_iff`.
The type-A component obstruction transported from the actual anisotropic
kernel gives a contradiction.

`localRankOneTypeD5_star_trivial_of_components` proves that every element of
the full absolute Galois group fixes every actual vertex in rank five.
The diagram-automorphism theorem `star_fixes_nonfork_of_D` fixes all vertices
with zero-based numbers below `3`, in particular the branching vertex `2`.
Exact marking puts vertex `2` and both fork tips in the zero subdiagram.
Each fork tip is adjacent to vertex `2`. The transported component-fixation
theorem consequently fixes each tip for the same full Galois element.
These statements cover every vertex.

`localRankOneTypeD_innerD5_of_five_le_of_components` combines the rank bound
with `5 ≤ n` to obtain `n = 5`. It combines the original exact marking and
the proved trivial full-star action with
`hasRankOneInnerD5Index_of_type_D_five`, obtaining precisely
`d.HasRankOneInnerD5Index`. The numbering has distinguished mathematical
vertex `2` and compares every actual Cartan entry.

The paired kernel-choice and Cartan modules explain the two transported
obstructions used here. This proof uses existing local marking results and
elementary Cartan arguments; it does not use the downstream local rank-one
classification or local Kneser--Tits. It retains arbitrary universes and
every field and residue characteristic, including characteristic two.
Rank four, its possible full-star images, and exceptional types are outside
this module.
