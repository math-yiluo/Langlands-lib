# Compactness through an open homomorphism

This internal topological reduction is derived from
`exists_isCompact_ker_coset_of_isOpenMap` in `OpenHomCocompactness`.
It is intended for the compactness step for actual centralizer norm kernels.
It supplies no algebraic quotient, anisotropy, or openness of a zero subgroup.

`compactSpace_of_isOpenMap_of_isCompact_ker` proves that a weakly locally compact
topological group is compact if it admits an open homomorphism into a compact
topological group with compact kernel. Neither surjectivity nor continuity of
that homomorphism is assumed. Applying the imported compact-coset lemma to the
whole source gives a compact set meeting every kernel coset. The whole source
is the product of that compact set and the compact kernel, hence is compact.

`isCompact_subgroup_of_isOpenMap_of_isCompact_inf_ker` applies this result to an
open subgroup. Its inclusion is an open map, so the restricted homomorphism
remains open. An open subgroup is closed; it inherits weak local compactness,
and the compact intersection with the original kernel pulls back to the compact
kernel of the restriction. Finally, the continuous subgroup inclusion maps the
compact whole subtype onto the original subgroup.
