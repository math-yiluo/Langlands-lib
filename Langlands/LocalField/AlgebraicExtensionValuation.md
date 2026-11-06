# The normalized additive valuation on an algebraic local-field extension

Author: Worker 1676.

This is a derived internal specialization of the published spectral valuation
`Langlands.LocalGalois.spectralValuation`, the compatible norm
`localNormedField`, the normalized integer order `FML.ord`, and the logarithmic
adapter `Langlands.LocalField.logAdditiveValuation`. It constructs an actual
valuation; no extension valuation is supplied as a premise.

Let `F` be any nonarchimedean local field with its given field, valuative
relation and topology, and let `L/F` be any algebraic field extension. The two
field universes are independent. No topology on `L` or characteristic assumption
on either field is imposed. The construction uses the complete ultrametric norm
on `F` already proved compatible with its supplied valuative relation.

`localLogScale F` is `-log ‖π‖`, where `π = uniformizer F` has integer order one.
`localLogScale_pos` proves it is strictly positive. The definition
`algebraicExtensionAddValuation F L` applies the normalized negative-logarithm
adapter to the actual spectral valuation on `L` with this scale.

The normalization proof first uses compatibility to show that base norm
comparisons are exactly reversed integer-order comparisons. Thus base elements
of equal integer order have equal norm. The base unit `π` has order one, so for
any `a : Fˣ`, equality of orders compares `a` with the integer power
`π ^ (fieldOrderUnits F a).toAdd`. Their norms coincide. The logarithm of this
integer power proves the exact normalization

\[
 \omega_L(a)=(\operatorname{fieldOrderUnits}_F(a)).\operatorname{toAdd}
 \quad\text{in }\mathbb R\cup\{\infty\}.
\]

This is `algebraicExtensionAddValuation_base_unit`. The theorem
`algebraicExtensionAddValuation_base_of_ord_eq` gives the same equality for
every base element with specified finite integer order. Zero has value infinity
by the bundled additive valuation laws. Finally,
`algebraicExtensionAddValuation_invariant` proves invariance under every
`F`-algebra automorphism of `L`, using Mathlib's spectral-norm invariance followed
by the logarithmic adapter's invariance theorem.

The scale is normalized to the base field rather than to a uniformizer of a
finite extension, so no extension ramification factor is silently inserted.
This module does not identify any actual root subgroup with an SU3 parameter
group, construct root valuation data for an arbitrary group, prove descent, or
prove the simply connected facet-fixing statement.
