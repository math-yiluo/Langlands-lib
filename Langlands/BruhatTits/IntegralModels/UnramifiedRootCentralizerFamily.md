# The actual finite family of unramified root and centralizer models

This internal derived unit assembles already constructed integral models
and their compatible maps. It uses no new existence input for the
individual root or centralizer models. All declarations retain arbitrary
universe `u`.

Supply maximal-unramified building data `C`, relative-component model
data `D`, an apartment subset `Ω`, and the equality identifying
`D.full.integralPoints` with the character-valuation kernel intersected
with its pointwise fixer. No boundedness or nonemptiness premise on `Ω`
is needed.

In namespace `UnramifiedRootCentralizerFamily`, `centralizerFullMap`
composes the constructed neutral-centralizer map with the actual
neutral-to-full inclusion. Its generic arrow is the original
`C.centralizer.j`, since the latter inclusion has identity generic arrow.
The family indexed by `Option (relativeRoots C.i)` selects that actual
centralizer at `none` and the actual root models constructed from the
integral apartment torus at `some a`. Each model is smooth, affine, and
has geometrically connected fibres, and each map is a compatible map to
the original full model.

`connectedFamily` enumerates this family by `Fin n`; finiteness comes
from the actual relative-root finiteness theorem. The model data and
generic inclusions are preserved by this enumeration.
`root_integralImage_eq_rootFixer` identifies each actual root-model image
with the actual root fixer by intersecting the full model's integral
points with the intrinsic root carrier and using the full fixer
equality. `integralImages_eq` then identifies the family's generated
integral images with `unramifiedNeutralRootCentralizerGroup`: the
constructed neutral centralizer image joined with the sharp fixer.

`integralPoints_eq_neutral_of_finiteRelIndex` is a conditional consequence.
It assumes `ConnectedGenerationStatement` and finite relative index of
this generated subgroup in the full model's integral points. It installs
the proved DVR, Henselian, and algebraically closed residue-field facts
for the actual unramified integer ring and applies
`FiniteConnectedModelFamily.integralImages_eq_neutral`. The remaining
positive congruence containment required there is discharged by the
proved openness and congruence-cofinality application, rather than taken
as another premise.

The unit does not prove finite relative index or the general
connected-generation statement. It does not identify the centralizer
integral points with a torus Iwahori subgroup or compare the resulting
neutral integral points with an arbitrary zero datum. These remain
obligations for the host parahoric-model target.
