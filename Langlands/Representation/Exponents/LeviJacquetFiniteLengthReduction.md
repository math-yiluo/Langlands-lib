# The represented-parabolic assembly for Renard VI.6.4

Author: Worker 1777. This internal supporting unit defines
`Langlands.Aubert.General.RepresentedParabolic.LeviJacquetFiniteLengthReductionStatement`
and proves it as `leviJacquetFiniteLength_reduction`. It retains four global
propositions as antecedents and does not prove the unconditional
`LeviJacquetFiniteLengthStatement`.

The independent universes are `u` for the field and rational-point groups and
`v` for the representation carriers. The conclusion is the existing closed
`LeviJacquetFiniteLengthStatement.{u, v}`, without any change to its
quantifiers, topology instances, actual represented parabolic, Levi and radical,
or normalized functor.

The four antecedents are the published propositions:

- `RationalPointsFiniteLengthAdmissibleStatement.{u, v}`;
- `SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, v}`;
- `LeviJacquetFiniteTypeStatement.{u, v}`;
- `ArbitraryParabolicJacquetAdmissibilityStatement.{u, v}`.

Their exact proofs remain separate obligations. This reduction is a consumer
assembly, and its publication would not complete the host proof task.

For a finite-length smooth representation `π` of `G(k)`, the proof extracts
Noetherianity of its actual group-algebra module using
`isFiniteLength_iff_isNoetherian_isArtinian`. The existing Noetherian-module
instance gives finite generation. The first antecedent gives admissibility of
`π`; the third gives finite generation of its Levi-valued normalized Jacquet
module.

The fourth antecedent gives admissibility of the normalized Jacquet module
valued in the literal subgroup `pointImage (l ≫ p)`. The proof transports this
admissibility to the actual group `rationalPoints M` using
`isAdmissible_comp_continuousMulEquiv` and the published topological group
equivalence `leviPointsEquiv p l hp hl`. The resulting representation is
definitionally the object of `leviJacquetFunctor`.

Finally, the second antecedent is applied to the connected reductive group
scheme `M`, using `hl.isConnectedReductive`. Its identity-test rational-point
carrier is the existing `rationalPoints M`, and its topology is definitionally
the installed `leviPointTopology l hl`. This yields finite length of the
unchanged Jacquet object. The argument includes the zero representation and
places no finite-dimensionality condition on the full carrier.

The provenance is internal: this file composes the named published interfaces
and Mathlib's finite-length/Noetherian comparison. The motivating original is
Renard 2026, VI.6.4, printed p.179 / PDF p.185, whose proof cites Howe VI.6.3,
VI.1.3, and the VI.6.1 corollary. The implementation makes explicit the finite
generation and the passage from the literal Levi image to its canonical
rational-point group. It supplies no proof of those cited inputs.
