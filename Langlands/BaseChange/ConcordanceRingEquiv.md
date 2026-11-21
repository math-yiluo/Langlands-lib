# Concordance under a change of coefficient rings

`concordanceRingEquiv` proves `ConcordanceRingEquivStatement`. It uses
topological fields \(F,F'\), topological commutative algebras \(E/F,E'/F'\)
with continuous scalar inclusions, and Borel measurable structures on
the four general linear groups. Ring isomorphisms \(F\to F'\) and
\(E\to E'\) are homeomorphisms. They commute with scalar inclusion
and intertwine the two chosen algebra automorphisms. The ordered norms
use the same length on both sides.

The induced entrywise isomorphisms of the matrix groups push forward
the supplied ambient measures. For these pushforwards, `ConcordAt` at
an image pair gives `ConcordAt` at the original pair with the tests
pulled back. The same pullback preserves `AreConcordant`, including
its vanishing assertion at regular elements outside the norm image.
The functions can be arbitrary complex-valued tests and the orbital
integrals use the Library's total Bochner convention.

The proof applies the ring maps entrywise to commute with the twist,
scalar extension, and the ordered norm. It transfers an associating
conjugator along the upper isomorphism. Pushing forward the defining
measure equality along that isomorphism gives association of the
transported centralizer measures. The twisted quotient change of
variables then compares both integrals for each compatible choice of
measures. To transfer the vanishing assertion, inverse matrix maps
transport the norm relation and mapping the characteristic polynomial
preserves separability. A companion lemma uses polynomial
irreducibility to transport regular ellipticity as well.

This is an internal change of variables for the associated measures and
concordance of Henniart–Lemaire, I.2.4–I.2.5 (printed pp. 14–18). It
applies to the coefficient isomorphisms used when a local cyclic
extension is realized at a place of a number-field extension.
