# Nilpotent rigidity of diagonalizable actions on arbitrary schemes

This is an internal extension of affine character-action nilpotent
rigidity to actual categorical scheme actions. The coordinate action uses an
arbitrary affine presentation over the base, so the acted-on affine scheme
requires no group structure.

Triviality on all algebras annihilating a nilpotent base ideal forces the
action and second projection to have the same underlying point map. Indeed,
test at the residue field of every point of the product. Each residue-field
algebra annihilates the ideal, since nilpotents vanish in fields. In particular
every open subscheme of the acted-on scheme is invariant.

The affine case transports the categorical action through an affine
presentation to the natural character action, then applies the homogeneous
projection rigidity theorem. This module proves the affine case and invariance of every open. These are
local ingredients for the arbitrary-scheme gluing argument; the module does not
assert the full arbitrary-scheme rigidity theorem, which is proved in
[`DiagonalizableActionNilpotentRigidity`](DiagonalizableActionNilpotentRigidity.md).
