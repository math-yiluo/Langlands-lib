# Local section transport through a sheaf isomorphism

This internal prerequisite uses the actual local module sheaves and determinant
polynomials from `LocalSectionBasis` and `LocalSectionDeterminant`. It is derived
from those constructions and Mathlib evaluation functors; it does not claim to
translate a separate theorem from the literature.

For a scheme `X`, an open `U`, and an actual isomorphism
`h : M.over U ≅ N.over U`, `localSectionIso h V` is the linear equivalence on
sections on each open `V` over `U`. Its maps are evaluations of `h.hom` and
`h.inv`, so evaluation commutes with restriction. A finite free chart `e` on `M`
gives the chart `e ≪≫ h` on `N`. Its section basis is proved to be the image of
the basis of `e` under this equivalence.

If local endomorphisms satisfy `a ≫ h.hom = h.hom ≫ b`, evaluation gives the
corresponding intertwining equation on sections. The matrices in the two
constructed bases coincide: the inverse section equivalence cancels the forward
one. Applying this to every member of a finite family proves equality of the
universal matrices and then their determinant polynomials on every smaller open.
The existing independence of finite trivializations extends this equality to
any finite target chart on the same open, including a different finite index
type.

All section rings may be arbitrary commutative rings, including rings with
nilpotents. No flatness, reducedness or characteristic hypothesis is imposed.
The local isomorphism and intertwining equation are explicit inputs; this
module does not construct a Lie base-change isomorphism or prove its naturality.
