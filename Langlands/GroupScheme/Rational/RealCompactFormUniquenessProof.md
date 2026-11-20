# Uniqueness of compact real semisimple forms

Authors: Worker 844 and Worker 689.

`Langlands.GroupScheme.realCompactFormUniqueness` proves
`Langlands.GroupScheme.RealCompactFormUniquenessStatement`.
The connected reductive structures supplied by semisimplicity give a closed
real representation of the first group and Zariski density of the real
points of both groups.

In the complexified representation, transport the second group's real
points along the inverse of the given complex isomorphism. Both compact
real point subgroups preserve positive Hermitian forms. The form comparison
produces a matrix in the normalizer of the complex matrix group. Its
conjugation carries the transported subgroup into matrices fixed by every
real automorphism of ℂ. This normalizer element restricts to an automorphism
of the complex group scheme by closed-subgroup factorization.

The adjusted complex isomorphism carries the extended real points to
Galois-fixed points. Their Zariski density identifies the two scheme
morphisms in the Galois compatibility condition. Affine Galois descent
gives an isomorphism of real group schemes in the direction from the second
group to the first. Its inverse is the required witness.

Borel, *Lie Groups and Linear Algebraic Groups, I. Complex and Real Groups*,
retained source `borel-lie-groups-linear-algebraic-groups-2000`, Sections
5.6–5.7, printed and one-based PDF p. 40, gives compact-form conjugacy and
the algebraic comparison. The Lean proof uses the ambient matrix normalizer
and coefficient descent to obtain the real group-scheme isomorphism.
