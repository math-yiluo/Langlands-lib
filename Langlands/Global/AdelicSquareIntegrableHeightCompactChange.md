# Height expansions under a finite change of compact

`AdelicSquareIntegrableHeightCompactChangeStatement` says that the
height-expansion predicates for two maximal Iwasawa compacts with the same
archimedean projection are equivalent. The proof
`adelicSquareIntegrableHeightCompactChange` applies the transfer in each
direction. This comparison uses the height expansions in Delorme,
*On the spectral theorem of Langlands* (2023), Lemma 3.10(i), and the
Iwasawa-coordinate definition of `A²_P` in Lapid, *On Arthur's asymptotic
inner product formula of truncated Eisenstein series* (2011), §2.

`HasSquareIntegrableHeightExpansion.of_compact_change` transfers a finite
square-integrable height expansion from one maximal Iwasawa compact to another
with the same archimedean projection. The inducing forms are first transferred
using `isSquareIntegrableInducedForm_of_compact_change`. On each clopen level
set of the difference of heights, the difference is constant and depends
only on the finite adelic coordinate, by
`IsIwasawaCompact.height_sub_pair_eq_of_infinite_eq`. Each cut inducing form is still
automorphic, retains its split-component covariance, and has a square integrable
restriction. The new scalar coefficient shifts its argument by the height
difference on that level set. There are finitely many level sets, so summing
their contributions gives the expansion for the second height.
