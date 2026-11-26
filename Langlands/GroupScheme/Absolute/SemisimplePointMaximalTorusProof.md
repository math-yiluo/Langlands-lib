# Semisimple points lie in maximal tori

`Langlands.GroupScheme.semisimplePointMaximalTorus` proves
`Langlands.GroupScheme.SemisimplePointMaximalTorusStatement.{u}`.
This is Corollary 17.36 on printed p. 363 of J. S. Milne, *Algebraic Groups*
(2017), source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

Start with a Borel subgroup containing the given point, using
`borelPointContainment`. Restrict a closed matrix representation of the
ambient group to that Borel. Its matrix at the lifted point is semisimple
by the hypothesis on the ambient point. Over an algebraically closed field
the eigenspaces span, so a basis drawn from their union gives a conjugate
closed embedding in which the point has diagonal matrix. The scheme-theoretic
intersection with the diagonal torus contains the lifted point by the
pullback property. Its projection to the diagonal torus is a closed
immersion, so `exists_diagonalizableIso_of_isClosedSubgroup_splitTorus`
identifies the intersection with a diagonalizable group. This gives the
diagonalizable subgroup used in Milne's proof.

Choose a maximal torus of the ambient group inside the Borel using
`borelMaximalTorus`. The Borel has a split torus quotient with smooth
unipotent kernel by `solvableTorusQuotient`, and `solvableSplitExtension`
gives a section. The chosen torus is maximal in the Borel as well, so its
map to the quotient is an isomorphism by `isIso_comp_of_section_of_isUnipotent`.
The inverse followed by the inclusion of the chosen torus gives a section
with image that torus. By `TrigonalizableSectionConjugacySmooth.exists_eq_comp_inner`,
the diagonalizable subgroup inclusion agrees with its map to the quotient
followed by this section and conjugation by a rational point of the kernel.
This implements the conjugacy step in Theorem 16.33(d) on printed p. 336.
Conjugation commutes with the inclusion of the Borel into the ambient group.
The conjugate of the chosen torus therefore remains maximal in the ambient
group and contains the original point.
