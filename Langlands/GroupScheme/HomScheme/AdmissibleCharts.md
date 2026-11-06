# Actual open charts of the admissible-subgroup presheaf

Author: Worker 1726.

This internal module constructs the map `OpenCharts.chartMap` from an actual
chart scheme to the total presheaf of admissible subgroup functors and proves
that it is a relatively representable open immersion.

Its universal section is the actual range of the supplied closed torus family,
encoded using `smallAdmissibleEquiv` and `OverTotal.ofFibre`. The theorem
`chartMap_app_of_over` identifies its value on every relative test with the
actual evaluation of that family. `chartMap_app_eq_iff` expresses equality with
an arbitrary total section as equality of these actual all-test subgroup
functors. Equality of total chart values first gives equality of their base
maps, after which the chart's evaluation injectivity proves
`chartMap_app_injective`.

`actualSubgroup` decodes a total section over its structural map.
`actualSubgroup_map` proves that decoding commutes with actual family
restriction, using total-to-fibre naturality and the small-presheaf restriction
identity. For a total section over an arbitrary scheme, choose its actual
closed torus representative. Apply `IsOpenChart.isOpen` to that representative.
The evaluation comparison above gives `exists_open_pullback`: after every
scheme map to the parameter scheme, the pulled-back total section is a chart
value exactly when the map's range lies in the resulting open subscheme.

To prove `isOpenImmersion_presheaf`, take a map from a scheme's Yoneda presheaf
to the total presheaf. Its Yoneda section gives this open subscheme. Its
inclusion has range inside that open, so the lifting criterion supplies a
morphism from the open subscheme to the chart. This forms the pullback square.
Commutativity follows from naturality. Uniqueness follows from monicity of the
open inclusion. Existence on arbitrary tests uses the same range criterion
and the open-immersion lifting property; chart injectivity identifies the
resulting chart morphism with the prescribed one. Mathlib's relative
representability criterion then supplies the asserted presheaf open immersion.

The constructions are internal consequences of actual evaluation, restriction,
the total-presheaf identities, Yoneda, and open-immersion lifting. They impose
no affine or reducedness restriction on parameter or test schemes. This module
does not assume sheafness, use field-point coverage, or construct the final
moduli scheme; those are separate steps of chart gluing.
