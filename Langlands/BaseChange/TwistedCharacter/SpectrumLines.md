# Disjoint spans of twisted irreducible character lines

Let `θ` be a group automorphism and assume that every open subgroup contains a
compact open subgroup preserved by `θ⁻¹`. The actual twisted distributions of
each admissible irreducible representation with a twisting isomorphism lie on
one line. The finite-family independence theorem makes any family of distinct
such lines linearly independent.

`disjoint_twistedSpectrumSpan` takes two predicates on representations whose
members are pairwise inequivalent across the predicates. It proves that their
spans of twisted irreducible distributions intersect only in zero. The proof
uses the existing `SmoothDualClass` and chooses one representative and one
twisting isomorphism for each class that admits such an isomorphism. Finite-family
independence gives independence of the whole indexed family by testing its
finite subsets. Every generator of either span is proportional to its chosen
representative's distribution by `exists_twistedDistribution_eq_smul_of_equiv`.
The two sets of classes are disjoint by the inequivalence hypothesis, so their
spans are disjoint by `LinearIndependent.disjoint_span_image`.

`exists_twistedSpectrum_projection` projects the full distribution space
onto the first span and kills the second. The quotient by the second span
is injective on the first by disjointness. A linear left inverse of the
restriction gives the projection. In particular, the projection acts by
identity or zero on a distribution supported entirely in one class or the
other.

This linear-algebra consequence of twisted character independence applies to
any pair of spectral conditions, for example an unramified orbit and its
complement. It uses the distribution-level form of Henniart–Lemaire (2011),
II.2.8, compared with Arthur–Clozel (1989), Chapter 1, Lemma 6.3, on the
independence of twisted characters.
