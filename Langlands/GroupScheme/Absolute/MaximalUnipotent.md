# Maximal smooth connected unipotent subgroups

Worker 883.

`IsMaximalUnipotentSubgroup i` means that `i` is a closed immersion, its source
is smooth, connected and unipotent, and every factorization through another
smooth connected unipotent closed subgroup is an isomorphism. It is
definitionally the local predicate in `AlgClosedQuotientSubgroupImageStatement`.
It describes connected unipotent subgroup varieties, as in Milne 2017,
Proposition 17.14 (printed p.356), which is the convention used in the
maximal unipotent clauses of Proposition 17.20 (pp.357–358).

The projection lemmas and the source and ambient isomorphism transport lemmas
unpack this definition. Source transport uses the published
`IsUnipotent.of_iso`; the remaining properties transport through the underlying
scheme isomorphism. Maximality follows by composing a competing factorization
with the inverse isomorphism.

`MaximalUnipotentExistence.exists_containing` extends any prescribed smooth
connected unipotent closed subgroup of an affine group locally of finite type
over a field to a maximal one. The proof adapts the published finite
coordinate-kernel-height argument for Borel existence. The coordinate kernel
of every smooth connected subgroup is prime and has finite height. Among the
unipotent overgroups of the prescribed subgroup choose one of least natural
height. An inclusion into another candidate reverses coordinate kernels, so
minimal height forces the ideals to coincide. The published
`BorelExistence.isIso_of_coordinateKernel_height_le` then makes the
factorization an isomorphism.

`exists_maximal` applies this construction to the trivial subgroup. These
existence lemmas are derived auxiliary results; they do not assume that the
field is algebraically closed or assert conjugacy or classification by Borels.
The import of `UnipotentRadicalMaximal` supplies only the trivial candidate and
the coordinate-height machinery; normality is absent from the new predicate
and from its minimization.

Source: James S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Propositions 17.14 and 17.20. The official errata snapshot of 2026-11-02
has no correction to these propositions.
