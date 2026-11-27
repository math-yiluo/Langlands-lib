# Local occurrence in an irreducible cuspidal summand

`Langlands.TraceFormula.groupSchemeCuspidalLocalOccurrence` proves
`Langlands.TraceFormula.GroupSchemeCuspidalLocalOccurrenceStatement.{u}`. The local carrier is
a subspace of a subspace of the supplied cuspidal summand, so it lies in the same universe
`u`. The map into the original cuspidal space is the composite of equivariant inclusions.

## Compactness of the cuspidal convolution

Work on the actual positive-central rational quotient with its Haar measure. For a compactly
supported continuous weight, `GroupSchemeQuotientL2CompactPart` constructs the operator obtained
by restricting the output to a compact subset. Its continuous kernel rows have uniformly
bounded norm there, so the restricted operator is Hilbert–Schmidt and compact.

`GroupSchemeQuotientL2ConvolutionOscillation` bounds the oscillation of the continuous
convolved representative under sufficiently small right translations by a prescribed
multiple of an `L²` function. The norm of this function is bounded by a constant times the
norm of the input. `groupSchemeFullAEL2ContinuousCuspidality` gives pointwise vanishing of
constant terms for that representative. `exists_compact_groupSchemeCuspDisplacementCover`
then bounds the value off a compact set by the same oscillation bound. The resulting
operator-norm estimate makes the convolution from the cusp space into the quotient `L²`
a limit of compact truncations. Orthogonal projection back to the cusp space recovers the
original cuspidal operator. [Cusp displacement](../Automorphic/GroupSchemeCuspDisplacement.md)

## Extracting the local representation

Restrict the right action to `P` and split the adelic group at `v` by `placeSplitting`. A
compact-open Haar average yields a nonzero local fixed vector. Some operator in a symmetric
approximate identity for the away action is nonzero on that vector. Denote this operator by
`B`. It commutes with the local group. For any compact open local subgroup `K` the integrated
action of the product of its indicator and the chosen away weight is compact. Its compression
to `P` acts on `P^K` as `B` times the nonzero volume of `K`. Thus `B` is compact on each
`P^K`. [Split integration and local extraction](IsotypicTrace/CuspidalCompactnessOccurrence.md)

The compact self-adjoint spectral theorem supplies a nonzero eigenvalue on a fixed space
where `B` is nonzero. Every compact-open fixed space in the smooth part of that eigenspace
is finite-dimensional, since it is an eigenspace for the same nonzero eigenvalue of a compact
operator. Van Dantzig's theorem gives finiteness at all open subgroups. The smooth eigenspace
inherits the invariant positive Hermitian form. Algebraic semisimplicity supplies an
irreducible admissible subrepresentation, and its inclusion realizes the asserted occurrence.
This extraction applies to every nonzero complete adelically invariant subspace of the
cuspidal space. [Fixed-space eigenspaces](IsotypicTrace/CompactFixedSpaceOccurrence.md)

## Source correspondence

- Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
  `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  Theorem 9.1.2, printed p. 241 (PDF p. 253), gives trace class for smooth cuspidal
  convolutions. This proof obtains compactness for continuous weights by truncation.
  The compact-part estimate uses bounded evaluation on a finite-measure region as in
  Lemma 9.3.3, printed pp. 247–248 (PDF pp. 259–260). The spectral step adapts the nonzero
  eigenspace argument in Lemma 9.3.1, printed p. 247 (PDF p. 259), to a commuting away
  convolution and the local fixed spaces.
- Mœglin and Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  `moeglin-waldspurger-1995-spectral-decomposition`,
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, SHA-256
  `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
  Section I.2.10, printed pp. 30–33 (PDF pp. 13–16), uses archimedean contraction of
  a maximal-parabolic radical in a deep simple-root direction and compact representatives
  at a finite level. Here contraction and rational invariance yield the small right
  displacements needed for the operator-norm truncation.
