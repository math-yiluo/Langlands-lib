# Schwartz–Bruhat majorants from archimedean decay and finite support

This internal helper combines `SchwartzCoordinateMajorant` with the Library's
definition of the adelic Schwartz–Bruhat space. It assumes an arbitrary family
of adelic rows with nonnegative real weights, uniform rapid bounds in their
archimedean coordinates, and one common finite denominator wherever the weight
is nonzero.

`denominatorRows` consists of finite rows whose coordinates become integral
after multiplication by a fixed rational element. The set is clopen, since
the integral finite adeles are open and closed. For a nonzero denominator it
is compact: it is the image of the product of integral finite adeles under
multiplication by the inverse denominator. Its characteristic function
`denominatorCutoff` is therefore locally constant with compact support.

`exists_schwartzBruhat_majorant` constructs a nonnegative real Schwartz
majorant of the archimedean family, converts it to a complex Schwartz map
through the continuous real linear inclusion, and multiplies it by that
finite cutoff. This is a pure Schwartz–Bruhat function, hence lies in the
defined complex span. At a nonzero family weight the finite cutoff is one,
so its norm majorizes the weight; zero weights are immediate.

The construction retains equality when every archimedean coordinate
magnitude agrees and finite integrality after the common denominator agrees
coordinate by coordinate. These are properties of the constructed function,
not additional regularity hypotheses on the family. No whole-group gauge
or convergence claim is made here.
