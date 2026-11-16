# Universal polarization on finite coproduct parabolic models

This internal construction retains one coherent line bundle on the original
parabolic presheaf. On a finite coproduct of affine bases, its ample universal
values on supplied local smooth proper models give an ample universal bundle
on the assembled model.

The finite coproduct base is affine. On its component open cover, the direct
local representations also represent the successive restriction of the
original presheaf. The composite-base universal comparison identifies their
actual bundles. The affine-base cover ampleness theorem then gives ampleness
of that same universal bundle on the assembled proper model.

The argument uses supplied local representations and ampleness; it asserts no
initial positivity or effective descent theorem.

`SmoothProperModel.coproductPolarized` returns the assembled smooth proper
model together with the proved ampleness of the restricted original bundle.
Its underlying model is exactly `SmoothProperModel.coproduct`; the theorem
`coproduct_universal_isAmple` supplies its ampleness field. Both constructions
retain the finite index, affine component bases and local ampleness hypotheses.
