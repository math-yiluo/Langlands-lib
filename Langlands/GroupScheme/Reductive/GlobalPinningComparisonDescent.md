# Descent of canonical pinned comparisons to the original groups

Worker 591, using Worker 686's actual affine chart models and transitions.
This is an internal adapter from supplied coherent root frames and an
explicit affine pinned isomorphism theorem premise.

For arbitrary groups over a scheme, `Descent.comparisonInOriginal`
conjugates an isomorphism between iterated chart pullbacks by the actual
direct/iterated pullback comparisons. Its endpoints are the direct
pullbacks of the two original groups. `comparisonInOriginal_pull`
proves compatibility with every further scheme pullback, including
specified equal base maps. The proof uses the actual pullback tower law.

For reductive groups with closed split fibrewise maximal tori, supplied
full global coordinate root data, chosen bases, and frames of every
actual root-weight module on every affine test,
`affineFrameIsoOver` normalizes the canonical fixed pinned comparison
between the two models on one affine chart. Its construction takes the
exact affine pinned isomorphism theorem and one full root-datum
equivalence matching the chosen bases as explicit inputs.
`affineFrameIsoOver_pull` follows from canonical comparison pullback
naturality and the generic normalization formula.

Assume both frame systems satisfy
`AffineRootFrames.IsCoherent`, namely coefficient extension preserves
the frame vector at one after projection to the original group's
dual-number points. `affineFrameIsoOver_independent` then proves that the
normalized comparison is independent of the affine chart on every common
scheme. It conjugates the fixed-comparison commuting square by the
original-group pullback comparisons and cancels the intermediate
isomorphisms. In particular, the common scheme need not be affine.

For any Type-u family of affine tests, `affineFrameIsoFamily` gives the
actual comparison of the original groups on each member. Pullback
naturality and chart independence establish the exact common-test
compatibility required by `Descent.CoverIsomorphism.IsCompatible`.
When the disjoint-union map of this family is flat, surjective and
locally of finite presentation, `globalIsoOfCoherentFrames` applies
covering-family descent to construct an actual global group-scheme
isomorphism. `globalIsoOfCoherentFrames_on_member` states exact recovery
of each supplied canonical chart isomorphism.

There are no affine, connected, noetherian or quasi-compact assumptions
on the original base or on common test schemes. The family and its
covering properties are supplied. This module does not construct the
global root data or coherent frames, prove the affine pinned theorem,
or assert torus/Borel preservation or the parent target.
