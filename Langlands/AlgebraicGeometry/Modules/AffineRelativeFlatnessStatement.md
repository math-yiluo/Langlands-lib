# The affine relative flatness criterion

`Langlands.AlgebraicGeometry.Modules.AffineRelativeFlatnessStatement` states the affine comparison needed to pass between relative flatness of actual module sheaves and algebraic module flatness in noetherian approximation.

For every pair of commutative rings R and B in the same arbitrary universe, every ring map φ : R → B, and every B-module M, the actual associated sheaf M~ on Spec B is flat over Spec R through Spec(φ) if and only if M is flat over R through φ. The left side uses the actual stalk action of the source local ring restricted along the actual scheme stalk map, as defined by `IsFlatOver`. The right side uses `Module.compHom M φ.hom`.

This is an internal comparison of the published `IsFlatOver` definition with Mathlib's associated sheaf and module flatness definitions. It adds no finite presentation, noetherianity, ambient flatness, or source module hypotheses. This file states the comparison; its proof is submitted separately.
