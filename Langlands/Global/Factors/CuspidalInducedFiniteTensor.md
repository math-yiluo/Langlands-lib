# The finite tensor of the prescribed cuspidally induced constituents

`source` is the normalized induction specified in
`CuspidalInducedConstituentAutomorphyStatement` at each finite place. The
completed-local and canonical matrix topologies agree, and the integral
matrix subgroup equals the spherical subgroup in the statement. These
comparisons let `assemble` apply `TensorSubquotient.ofLocalSubquotients` to
the given local subquotient and spherical hypotheses.

The target finite-adelic tensor is irreducible by the local irreducibility
and admissibility of the prescribed factors. An injective intertwiner from
this tensor to the finite restriction of an actual irreducible operator
subquotient gives every requested completed-local embedding. For each place
use `exists_injective_localTensorEmbedding`, then compose with the finite
intertwiner restricted to the corresponding local inclusion.

This is the finite part of the construction in R. P. Langlands,
*On the notion of an automorphic representation* (1979), Lemma 1, printed
p. 203, PDF p. 198 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`). Geometric induction
and Proposition 2 supply the global realization step in the planned proof.
