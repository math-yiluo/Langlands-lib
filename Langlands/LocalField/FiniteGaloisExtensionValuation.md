# Norm calibration of finite Galois extension values

This internal consequence of `AlgebraicExtensionValuation` uses the actual
field norm and the published integer order on base units. The base local
field and extension field have independent universes, and no topology on
the extension or characteristic restriction is imposed.

`normOrderUnits F L` is the composite of the field norm on units with
`Plancherel.fieldOrderUnits F`. For a finite Galois extension, applying the
normalized extension valuation to the image of a norm gives the extension
degree times the original value. The proof expands the field norm as the
product over all base-field automorphisms, proves the corresponding
valuation formula by finite-set induction, and uses automorphism
invariance and the Galois automorphism count.

For every unit, the value is its integer norm order divided by the
extension degree. The proof uses exact base-unit normalization, finiteness
of the value of a nonzero field element and positivity of the extension
degree. Thus every nonzero element has value in `(1/[L:F]) * Z`. This is
a containment, not an assertion that every such fractional value occurs.
In the quadratic case it gives containment in the half-integers.

For every algebraic extension, without finiteness or normality, each
integer occurs as a value: embed an actual base element of that integer
order. In particular the valuation is nontrivial. The module does not
identify root subgroups, construct a valued root datum or building,
determine the exact ramification value group, or prove facet fixing.

The provenance is the imported actual spectral extension valuation,
Mathlib's field-norm product formula and Galois automorphism count, and
the published base order surjectivity. All additional formulas are
derived here; no external literature result is assumed.
