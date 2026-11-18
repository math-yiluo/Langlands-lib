# Detecting multiplicative type on ordinary local affine limits

Worker 875.

`Langlands.GroupScheme.LocalMultiplicativeType.diagonalizingCover` constructs
an actual affine fppf diagonalizing cover of an affine base from relative
multiplicative type on one supplied `LocalEtaleLimit` at each point. The group
is affine and locally of finite presentation over the base. Flatness of the
group is not required. The local condition is relative multiplicative type,
expressed by an actual fppf diagonalizing cover; no global diagonalization
over the local ring is assumed.

The implementation first chooses an affine fppf diagonalizing piece through
the local ring's closed point (`exists_affine_diagonalizing_piece`).
`FlatAffineLimit.model` descends this flat affine finite-presentation piece
to a level with an actual recovery square. Restricting to the over category
of that level preserves the limit. Base-changing the diagram along the model
produces an affine diagram whose limit is the original diagonalizing piece.
Generic affine-limit group-isomorphism descent then spreads its isomorphism
with the fixed diagonalizable group to a further level.

`exists_fppf_diagonalizing_neighbourhood` retains a point on the resulting
level over the original base point. Its morphism to the base is flat and
locally of finite presentation, since it is a base change of the model map
followed by an etale diagram structural map. It need not be etale or individually
surjective. Choosing a neighbourhood per point gives the actual cover in
`diagonalizingCover`; `of_pointwise_localBaseChange` reads relative
multiplicative type from this cover.

`of_localizations` applies this construction over `Spec R` to the actual
`LocalEtaleLimit.ofLocalization R p` for every prime `p`. Thus an affine locally
finitely presented group is of relative multiplicative type if it has that
property after localization at every prime. `localLimitOfAffine` transports
the ordinary localization presentation through an affine scheme's spectrum
isomorphism. `of_all_localBaseChanges` uses these presentations on an affine
open cover to prove the arbitrary-base implication: an affine locally finitely
presented group is of relative multiplicative type if it is so after every map
from the spectrum of an ordinary local ring. There is no strict-henselization
existence premise in these results.

This is an internal combination of explicit cover refinement, the included
flat affine model and group-isomorphism spreading constructions, the actual
localization diagram construction, and published fppf/open-cover locality.
The proof uses only ordinary locality of the limit ring. Strict-local data
can also be supplied by its forgetful map to `LocalEtaleLimit`.
The fibral criterion, complete-local deformation theorem and whole host
fpqc extension theorem remain separate proof obligations.
