# Finite affine section covers in one positive degree

`FiniteAffinePowerSectionCover L` records a positive integer `degree`, a natural
number `dimension`, and `dimension + 1` actual sections of the actual tensor
power of `L`. Their whole generation opens are affine and cover `X`.
`LineBundle.IsAmple.finiteAffinePowerSectionCover` chooses such data from the
published definition of ampleness, in every universe and on an arbitrary scheme.

The construction first chooses the pointwise sections supplied by ampleness and
uses compactness to retain finitely many of their affine generation opens. It
adjoins a zero section of the first tensor power. Its generation open is empty,
which is affine, and this ensures that the index family is nonempty even when
`X` is empty. The published `exists_common_degree` raises the finitely many
sections to powers of a single common positive degree without changing their
whole generation opens. A finite equivalence then indexes them by
`Fin (dimension + 1)`.

This is an internal construction derived from `LineBundle.IsAmple`, the common
degree lemma in `Picard/FiniteFieldExtensionAmpleExistenceDescentProof`, and the
zero-section generation-open theorem in `Picard/LineBundleSectionVanishingProof`.
It has no additional literature input. It supplies the finite linear-system
data needed for fixed-bundle ampleness spreading, but proves no spreading or
section-lifting assertion.
