# Reduction of actual geometric terms to standard restricted functors

This internal construction combines the source Jacquet and target induction
reductions, retaining arbitrary and potentially different fine source and target
indices. The acting groups are the actual subgroups of the ambient group.

`conjugationK0_subgroup_eq` proves that the equality identifications of two
source subgroups and two target subgroups commute with inverse conjugation by
the same ambient element. The proof composes the actual continuous group
equivalences, proves their equality on elements, and applies exact-K0 pullback
functoriality. Thus the equality holds on every virtual finite-length class.

`standardIntersectionTermK0` is the composite of literal restricted normalized
Jacquet restriction inside the coarse source Levi, its canonical subgroupOf
identification, actual inverse-conjugation pullback between the fine Levis,
the target subgroupOf identification, and literal restricted normalized induction
inside the coarse target Levi. The source and target preservation pairs are
explicit inputs, as is actual conjugation membership. No abstract relabeling is
used in place of an actual group map.

`geometricTermFiniteLengthOfEq` derives finite-length and short-exact
preservation for the actual geometric factors from those standard preservation
pairs and the supplied subgroup identities. `geometricTermK0_eq_standardOfEq`
then identifies the full actual geometric-term map with
`standardIntersectionTermK0`. It uses the source and target comparison
identities, commutes the equality transports past conjugation, and evaluates the
composite maps on an arbitrary virtual class. The conclusion allows any preservation witnesses for
the actual term; their choice is irrelevant because they are proofs of
propositions.

The label, ambient group and representation universes are independent. The
terms use representation carriers in `max uG uV`, so actual target induction
stays in that universe. All topologies are inherited and all normalized
functors retain their actual Haar-modulus characters. No Coxeter, finiteness
or reductivity hypothesis is needed for this equality-based construction.

The source and target intersection identities and their semidirect
decompositions remain explicit hypotheses. This module does not establish
those geometric identities, transitivity of Jacquet restriction, the geometric
expansion, dependence on a common finite label, the longest representative
comparison, or the whole rational-point Jacquet compatibility proposition.
The construction is internal; its proof uses the named comparison modules and
exact-K0 functoriality, without an external mathematical assertion.
