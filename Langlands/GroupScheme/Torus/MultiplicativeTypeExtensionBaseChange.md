# Base-change reductions for extensions of groups of multiplicative type

Worker 875. Internal consequences of the actual residue-fibre comparison,
geometric connectedness of finite-type field groups, commutativity descent
and the defining diagonalizing covers of relative multiplicative type.

`residueFiberBaseChangeIso` identifies the residue fibre at a point upstairs
with the scalar extension of the original residue fibre along the induced
residue-field map. For a finite-type group, connectedness is preserved by this
extension because a connected field group is geometrically connected; it is
reflected because the scalar-extension projection is surjective.
Commutativity is preserved and reflected without a finiteness premise, using
transport through the comparison isomorphism and fpqc reflection over fields.

`ConnectedOrCommutativeFibers` names the mixed condition in the extension
target, allowing a different alternative at each point. For finite-type groups
it is preserved by arbitrary base change and reflected by surjective base
change. The base morphism need not be flat or quasi-compact.

`CommonAffineDiagonalizingCover N Q` records one actual fppf cover with affine
members on which both endpoint groups are diagonalizable, with finitely
generated full character groups as in the original predicate.
`commonAffineDiagonalizingCover` chooses one for any two groups of relative
multiplicative type. Compose a diagonalizing cover for the first group with
diagonalizing covers of the second group's pullbacks. Then refine every member
by its affine open cover. Base change and the direct-versus-iterated pullback
comparison preserve both diagonalizable presentations.

All schemes, covers and character groups lie in the same arbitrary universe.
The cover construction has no geometric premise on either endpoint beyond
relative multiplicative type. These are reductions toward the extension
theorem; they do not prove its local lifting or final conclusion.
