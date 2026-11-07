# Detection of the actual quotient-isomorphism property after field extension

Worker 1317. This is internal support for the split Steinberg quotient proof,
derived from the published actual class-function quotient base-change theorem,
fpqc descent of scheme isomorphisms, and faithful flatness of field extensions.
It makes no external source claim and does not duplicate the field-base-change
construction.

For arbitrary fields `K` and `F` in the same arbitrary universe, an algebra
structure `Algebra K F`, an affine actual group scheme `G` over `K`, and any
supplied morphism `f : X ⟶ G.X` from a scheme over `K`,
`ClassFunctions.BaseChange.quotientComposite` is literally the scalar extension
of `f` followed by the actual canonical quotient map of the scalar-extended group.

`quotientComposite_eq` identifies this morphism with the pullback of
`f ≫ ClassFunctions.rho G` followed by the published
`ClassFunctions.BaseChange.quotientComparison` isomorphism. The equality uses the
published `quotientComparison_rho` diagram and functoriality of pullback; the
quotient and its map remain the actual fixed equalizer construction.

The private fpqc reflection helper constructs the actual pullback square of a
morphism in the over category. Mathlib's descent of scheme isomorphisms along
surjective flat quasi-compact maps reflects invertibility of the underlying
scheme morphism, and the forgetful functor reflects it in the over category.
The spectrum of a field extension is fpqc by `fieldExtension_fpqc`. Composing
with the quotient comparison therefore gives
`isIso_quotientComposite_iff`: the scalar-extended morphism followed by the new
quotient is invertible exactly when the original morphism followed by its
quotient is invertible. The forward implication uses fpqc reflection; the
reverse implication uses preservation of isomorphisms by pullback. No
reductivity, splitness, characteristic, perfectness, infinitude, or algebraic
closedness assumption is needed.

`SplitPinning.isIso_steinbergQuotient_fieldExtension_iff` specializes this result
to the exact original `steinbergProduct e x n`, retaining every supplied ordering,
normalized root family and reflection-representative family. It does not
construct a pinning or root family over the new field or identify that pulled-back
morphism with a new supplied-data product. That comparison and the actual
quotient-isomorphism proof remain separate obligations.
