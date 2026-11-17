# Explicit regularized four-crossing families

This internal unit applies the scalar normalization and finite-layer analytic
tools to the four actual Frobenius crossings at fixed endpoint exponents.
Its inputs are the published generic and erased-denominator product formulas,
parity restriction, symmetric Frobenius maps, compact polynomial-degree layers,
and algebraic weak derivatives. It introduces no analytic continuation axiom.

`ValidChoice ν ε none` requires the parameter to avoid every negative
denominator root. `ValidChoice ν ε (some r)` requires it to equal the negative
root with index `r`. The scalar family `multiplier ν ε c z` uses the generic
formula at `ν + z` for `none`, and the erased-denominator formula there for
`some r`. Both formulas are restricted to the specified parity class.

The family is reflection symmetric for every parameter. A valid choice makes
each scalar coordinate analytic at zero and makes the value at zero recurrent
at `ν + 1`. For a removed denominator, its linear factor at `ν + z` is exactly
`z`. Thus away from zero and on the specified parity class the scalar family is
`z ^ order c` times the generic multiplier, where the order is zero or one.
At a positive exceptional generic center, parity restriction gives a finite
support bound with cutoff `ε.toNat + 2r + 1`.

`Choices` supplies one such option for each of `BC`, `AC`, `BD` and `AD`.
`Valid d e c` requires each choice to be valid for its actual constituent
exponent difference and parity. It allows several removed denominators; this
unit does not assert that an unlinked pair has at most one pole.

The four `crossingData` instances use only reflection symmetry and define
actual Frobenius maps for every complex parameter on the fixed expanded
character spaces. `fullMap` composes the crossings in order `1, 0, 2, 1`.
`rawMap` restricts its source to the two original induction windows.
Neither definition assumes that the shifted sequences satisfy recurrence
away from the center.

Every member of the ambient family preserves each compact polynomial-degree
layer. For valid choices, applying `fullMap` to a weakly analytic input family
in one fixed layer gives a weakly analytic output at zero. The proof applies
`weaklyAnalyticAt_blockFrobMap` four times and retains the same degree bound.
Every fixed source vector lies in a degree layer after inclusion in the
expanded source. Consequently `rawMap` applied to that vector is weakly
analytic at zero, and its entire output family lies in one finite-dimensional
target layer.

`rawMap_has_derivative` applies the finite-layer derivative construction to
these actual families. `normalizedMap` is the linear quotient `z⁻¹ • rawMap z`
away from zero and the resulting derivative map at zero. This defines the
candidate normalized value; analyticity of this quotient additionally needs
vanishing of `rawMap 0`, which is not proved here.

Finally `atZero` packages the four center sequences as the existing recurrent
crossings. `rawMap_zero_eq_recurrent` identifies the center value with their
actual recurrent composite, providing the interface for the separate
finite-support residue-cancellation theorems.

The file does not prove residue cancellation, equality of the composite with
a scaled generic shifted map, target induction-window membership after
division, inverse identities at the exceptional parameter, or limiting Lie
intertwining. In particular it does not prove `RealInducedSwapStatement`.
