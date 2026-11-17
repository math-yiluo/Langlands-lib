# Finite character-degree tests for diagonalizable normalizers

This internal algebraic unit gives one finite character-degree test for the
full normalizer family of an embedded diagonalizable group. It assumes a
corepresented ambient group functor, a finitely generated abelian character
group, and a finitely generated ideal cutting out the embedded group on all
coefficient algebras. It imposes no noetherian or smoothness assumption.

`FiniteDegreeDetectsNormalizer emb n` says that a point normalizes the full
embedded character family if and only if the universal conjugate, for both
that point and its inverse, belongs to the embedded family after reduction
of character degrees modulo the subgroup of n-fold multiples. The theorem
`exists_finiteDegreeDetectsNormalizer` produces one positive integer n that
works for every coefficient algebra and every parameter point. This degree
quotient is finite by the separate finite-character separation lemma.

The proof defines coefficient-preserving degree change and proves its
agreement with the usual group-algebra pushforward. Normalization after
every algebra refinement is first reduced to membership of the two universal
conjugates. Evaluation of the universal character recovers every further
test character.

Choose finite generators of the subgroup ideal. At the universal ambient
point, collect the character supports of the classifying functions of both
universal conjugates on these generators. One integer degree quotient is
injective on that finite union of supports. Every other parameter point is
a coefficient specialization of the universal one, which can only shrink
these supports. Vanishing after degree reduction thus implies vanishing
before reduction on the ideal generators and hence on the whole ideal. The
reverse implication is preservation of subgroup membership under algebra
maps.

The resulting criterion still tests membership in the full embedded group
over a finite group-algebra test. Identification with the normalizer of the
finite torsion subgroup and construction of a normalizer homogeneous quotient
remain separate assertions.
