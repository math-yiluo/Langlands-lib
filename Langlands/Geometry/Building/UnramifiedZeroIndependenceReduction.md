# Independence of zero subgroups conditional on sharp torus conjugacy

This internal assembly works at arbitrary universe `u`. Its explicit global
premise is `UnramifiedSharpTorusConjugacyStatement.{u}`. It derives the exact
`UnramifiedZeroPointsIndependenceStatement.{u}` from that premise and constructs
the identity multiplicative equivalence between the actual zero subgroups
defined by two arbitrary `UnramifiedZeroDatum F H`.

The theorem `unramifiedZeroPointsIndependence_of_sharpConjugacy` applies sharp
conjugacy to the simply connected derived cover of the first datum and the two
chosen maximally split maximal tori. This gives a point in the first datum's
actual simply connected image and an isomorphism between the two torus
presentations satisfying the conjugation triangle.
`UnramifiedZeroDatum.torusIwahori_map_eq_of_iso` proves compatibility of their
torus norm subgroups for their independently chosen finite Galois splitting
fields. `zeroPoints_eq_of_sharp_torus_iso` then gives equality of the two actual
zero subgroups. That comparison already accounts for the independently chosen
simply connected covers.

`UnramifiedZeroDatum.zeroPointsEquivOfSharpConjugacy` applies
`MulEquiv.subgroupCongr` to this equality. It is a concrete multiplicative
equivalence preserving the underlying rational point. The theorem
`zeroPointsEquivOfSharpConjugacy_coe` records this identity by reflexivity.

The provenance is internal: the module assembles the published subgroup
comparison and arbitrary-splitting-field torus norm comparison. It supplies
the final algebraic implication for the independence part of Kaletha–Prasad
Lemma 2.6.24, without adding a premise to either imported statement or changing
their definitions. It does not prove sharp conjugacy. The unconditional
independence proof still requires a proof of that geometric statement; the
conditional theorem and equivalence here do not discharge that obligation.
