# Local tensor contractions on pure sections

This derived module introduces `pureSection`, the image of a pure sectionwise
tensor in the actual sheaf tensor. It proves compatibility with restriction,
with morphisms in both factors, and with the right tensor unitor.

`lineRestrictionIso` expresses a genuine local line trivialization with codomain
the restriction of the original structure module. `lineCoordinates` evaluates
that chart on each smaller original open as an actual linear equivalence.
Its action agrees with the previously constructed `modE` section transport.

`tensorRestrictionTrivialization_pureSection` computes the actual contraction
on the image of a restricted pure tensor: it multiplies the first section by
the scalar obtained by applying the line chart to the second. The proof cancels
the invertible restriction comparison, applies naturality of the tensor
sheafification unit, and evaluates the right unitor.

These are internal consequences of the existing sheafification adjunction and
restriction comparison. Cross-open contraction comparison and the ordinary
moduli representability theorem remain further obligations.

`pureSection` is a transparent alias of `BiCech.tsec` from
`Modules/BiCech/TensorFrame`, with the module and open arguments explicit.
It uses that existing section operation throughout the contraction formulas.
