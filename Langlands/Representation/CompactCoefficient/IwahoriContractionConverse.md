# Compact restriction coefficients and escaping Iwahori contractions

This internal unit isolates a representation-theoretic argument used in the
compact-restriction converse of Renard VI.2.1. It is derived from the published
compact-coefficient predicate, finite-orbit averaging, the linear-algebra
sequence lemma in `CuspidalSupport.HarishChandraConverseProof`, and the abstract
Iwahori compression theorem in `Jacquet.IwahoriContractionAdmissibility`.

The group and representation-carrier universes are independent. The ambient
group is an arbitrary topological group. The subgroup has the inherited
topology, and the representation is smooth and complex. No admissibility,
finite-dimensionality, normality, or openness of the subgroup is required.

`EscapesCompactSets x` means that the sequence eventually leaves each compact
set. Its continuous-map lemma observes that escape of the image sequence
implies escape in the source, since a continuous image of a compact set is
compact.

For an arbitrary algebraic functional `ℓ`, compose `ℓ` with the compact average
over the specified compact open ambient subgroup `K`. The resulting functional
is smooth for the restricted dual: the inverse image of `K` fixes it, by right
invariance of the average. Compactness of this coefficient makes its values
eventually zero along any escaping sequence in the subgroup. The published
linear-algebra lemma then shows that some term of the averaged vector sequence
is zero. This proves `exists_average_eq_zero_of_compact_restriction`.

For a `K`-fixed vector and an Iwahori contraction `g` in the subgroup, apply that
result to the powers of `g`. Multiplicativity of compressed powers places the
vector in the generalized kernel of compression. The published identity of
that kernel with the kernel of the actual fixed Jacquet quotient map proves
`mk_eq_zero_of_escaping_iwahoriContraction`.

`HasEscapingIwahoriContractionBasis` explicitly requires such compact open
levels below every ambient open subgroup, with contraction elements in the
specified subgroup and escaping powers. Smoothness then permits choosing a
level fixing each vector. All its Jacquet classes vanish, so the actual
coinvariant space is a subsingleton.

The basis is an explicit hypothesis of this generic helper. This unit does not
construct it for rational points or for the actual rational norm kernel, and
does not prove the general compact-restriction converse or common fixed-level
coefficient support. Those geometric and uniformity obligations remain in the
unchanged application targets.
