# Normality in fpqc quotient squares

These are internal descent lemmas for actual group schemes over an arbitrary
base scheme and in an arbitrary universe.

`mem_range_of_local_quotient_lift` tests membership in the range of a monic
group-scheme homomorphism after locally lifting one chosen quotient point.
The quotient map must be flat, surjective as a scheme morphism, and
quasi-compact. The proof pulls back that quotient along the chosen point.
Its projection is an effective epimorphism, so the published
`mem_range_of_comp_mem_range` descends the membership.

`isNormal_range_of_fpqc_square` considers a commuting square
`i ≫ q = p ≫ j`, with both vertical maps `q` and `p` fpqc and with
`j` monic. If the all-test range of `i` is normal, then the all-test range of
`j` is normal. Given an ambient quotient point and a point of the quotient
subgroup, the proof lifts them successively along `q` and `p`. Normality
upstairs gives a conjugate in the original subgroup. The commuting square
maps it to the required conjugate downstairs, and two applications of
membership descent finish the proof.

Neither map is required to be smooth. Lifts are taken after genuine fpqc
pullbacks of test schemes; surjectivity on the original test's points is
not assumed. The lemma does not require that the original subgroup contain
the ambient kernel or construct either quotient.
