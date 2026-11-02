# Ampleness of the actual canonical diagonal bundle and its cube

`canonicalCubicBundleAmple` proves
`CanonicalCubicBundleAmpleStatement` in arbitrary universe `u`. For every
ordinary polarized datum over any field, both its specified canonical diagonal
Poincaré bundle and its actual tensor cube are ample over the original field.

The helper `poincareDiagonal_isAmple_of_fieldPresentation` starts with the
published ample-Mumford presentation predicate for a specified map. The
published `poincareDiagonal_isAmple_after_fieldExtension` gives ampleness of
the actual pullback of its diagonal bundle after some field extension.
`fieldBaseChangeAmpleReflection` then gives ampleness of that same fixed
bundle over the presentation field.

`Datum.canonicalBundle_isAmple` takes an algebraic closure `F` of the original
field `K` and its canonical map `b : Spec F → Spec K`. The datum's existing
relative polarization field, evaluated at `F` and `b`, supplies precisely the
ample-Mumford presentation of the canonically changed map and dual. Apply the
first helper to this map. Transport ampleness along the actual
`poincareDiagonalBaseChangeIso` to the pullback of `a.canonicalBundle` along
the base-change projection. A second use of fixed-bundle reflection gives
ampleness of `a.canonicalBundle` itself over `K`.

`Datum.cubicBundle_isAmple` applies the published
`Datum.cubicBundle_isAmple_of_canonicalBundle`, which uses positive tensor
power ampleness with exponent three on the actual cube. The final named
theorem pairs the two conclusions.

This proof is an internal assembly of the imported field presentation,
actual base-change isomorphism, fixed-bundle reflection and positive tensor
power results. It adds no ampleness or geometric premise. Algebraic closure
is used internally to evaluate the existing relative polarization predicate;
the original field need not be algebraically closed. The dimension, degree
and level fields of the datum need no additional conditions. The proof
establishes no cohomology vanishing, multiplication degree, Euler-square
identity or dimension formula.
