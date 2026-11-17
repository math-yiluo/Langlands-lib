# Determinant transitions of actual adapted jet frames

This internal unit computes transitions between the actual adapted jet
sheaf frames constructed on two affine cotangent frame charts. Let `G`
be a smooth affine group scheme over an arbitrary scheme `S`. Supply
affine opens `U,V`, actual cotangent frames on them with the same finite
index type `σ`, and augmentation-ideal lifts of each frame's cotangent
section basis. No compatibility of those lift systems is assumed.

`cotangentOverlapMatrix` is the actual change-of-basis matrix of the two
cotangent sheaf frames on an open `W ≤ U,V`. `adaptedOverlapMatrix` is
the actual change-of-basis matrix of the two corresponding adapted
identity-jet sheaf frames on the same open. These definitions use the
section bases of actual sheaf isomorphisms.

The theorem `adaptedOverlapMatrix_det` proves, for every such open `W`,

`det(adaptedOverlapMatrix n) =
  det(cotangentOverlapMatrix) ^ jetExponent σ n`.

For affine `W`, the proof chooses one temporary adapted affine jet basis
using the first cotangent frame's basis on `W`. The semilinear actual
restriction determinant formula says that the first chart's adapted
vectors have determinant one in this temporary basis. The corresponding
determinant for the second chart is the cotangent transition determinant
to the stated exponent. Multiplicativity of change-of-basis matrices
then cancels the determinant one and gives the actual frame transition
formula. The temporary lifts and truncation splittings need not be
related to either chart's choices.

For arbitrary `W`, actual section-basis coordinates commute with
restriction. Consequently both matrix determinants, and the asserted
power, restrict to their affine-subopen versions. The structure module's
sheaf separation on the affine-open basis extends the equality to `W`.
In particular the result applies to the full overlap `U ∩ V`, whether
or not that overlap is affine.

The exponent and its positivity at positive jet order are the existing
algebraic ones. The hypothesis that the two supplied frames have the
same index type is retained; this module makes no global constant-rank
assertion. Its provenance is internal: the proof uses actual frame and
restriction calculations, matrix multiplicativity and sheaf separation.
It provides determinant transition equality for line-bundle gluing but
does not itself construct a determinant line isomorphism or prove
ampleness.
