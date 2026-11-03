# Dynamic normalized functors in a closed represented subgroup

This internal adapter identifies the actual normalized induction and Jacquet
functors in a closed representative with those in its literal subgroup of
ambient points. It supports the actual-Levi comparison in the proof task for
Renard VI.6.2. It proves comparison and finite-length equivalence, without
asserting finite length of induction.

The underlying inputs are a topological commutative ring `R`, affine group
schemes `G` and `L`, a subgroup functor `S` of `G`, and a closed inclusion
`j : L ⟶ G` representing `S`. The point topologies are the canonical
`rationalPointTopology`. The map `pointEquiv` is the published multiplicative
homeomorphism from the points of `L` onto the literal subgroup `S` of points
of `G`, and its underlying map is postcomposition by `j`.

For any cocharacter `ν` of `L`, the published closed-subgroup pullback laws
identify its parabolic, centralizer and unipotent subgroups with the pullbacks
of the corresponding subgroups for `ν ≫ j`. The three membership lemmas
express these laws inside the literal subgroup `S`.

`GroupTransport.semidirectDecomposition` transports a given semidirect
decomposition across a multiplicative equivalence with three specified
subgroup membership compatibilities. Normalization is transported by the
group law. Existence and uniqueness of the Levi component follow from the
source projection and its characterization by membership of `m⁻¹ p` in the
radical. Applying this to the representative's dynamic decomposition gives
`insideDecomposition`; separatedness of `L` is the hypothesis of that
published dynamic decomposition.

`centralizerEquiv` restricts `pointEquiv` to the corresponding dynamic
centralizers. `unipotentClosed` pulls back closedness of the ambient radical
for `ν ≫ j` to the radical for `ν`. With local compactness of the ambient point
group and closedness of the represented subgroup, the theorem
`representative_locallyCompactSpace` transfers local compactness to the
representative. With a nonarchimedean ambient point group,
`representative_nonarchimedeanGroup` transfers that structure to the
representative. In both cases the topology remains the pinned point topology.
Closedness of the represented subgroup over a Hausdorff `R` can be supplied by
the published `isClosed_rationalPoint_subgroup`.

For the functor comparisons, the literal represented subgroup and the
representative point group must each be locally compact nonarchimedean groups,
and the ambient radical for `ν ≫ j` must be closed. The preceding results
provide the required topology and closedness transfers where their stated
hypotheses hold. Under separatedness of `L`, `inductionIso` identifies
normalized induction in the literal subgroup, followed by pullback to the
representative, with pullback on the Levi followed by normalized induction in
the representative. `jacquetIso` gives the corresponding natural isomorphism
for normalized Jacquet restriction.

These definitions specialize the published `GroupTransport.inductionIso` and
`GroupTransport.jacquetIso`. Those constructions compare the actual semidirect
projections by uniqueness and the Haar half characters by conjugacy of the
radical automorphisms. Thus the induction comparison uses the full-parabolic
Haar character on both sides; no replacement by a Levi-inflated character is
assumed. The formula `inductionIso_hom_eval` says that the map on induced
functions is precomposition by `pointEquiv`. The formula `jacquetIso_hom_mk`
says that the map on coinvariants keeps the vector representative.

`induction_hasFiniteLength_iff` proves equivalence of finite group-algebra
length for the two compared normalized induced objects. Its proof first
uses the published finite-length equivalence for pullback along a surjective
group homomorphism, then transfers finite length through the component of
`inductionIso` in either direction. The input carrier universe `uV` is
independent of the ring/group universe `u`; the induction output carrier is
in `Type (max u uV)`, while Jacquet restriction retains `uV`.

These are derived constructions from the published point homeomorphism,
closed-subgroup pullback laws, dynamic semidirect decomposition, normalized
functor transport and finite-length transport. They do not claim a separate
literature assertion. They do not establish that a representative is reductive,
realize source parabolics by ambient cocharacters, or prove the
representation-theoretic finite-length prerequisites of VI.6.2.
