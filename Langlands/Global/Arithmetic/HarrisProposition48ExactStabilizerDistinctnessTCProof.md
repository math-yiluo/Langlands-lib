# Distinct Mackey components from totally complex B6

`Langlands.Global.Harris.proposition48ExactStabilizerDistinctnessTC` proves
`Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV}` with the original
hypotheses at independent universe levels `uF` and `uV`.

The proof applies `proposition48ExactStabilizerDistinctnessTCReduction` to
`Langlands.Automorphic.cuspidalArithmeticSpectralTransport.{0, 0, uV}`. As in
the general reduction, spectral transport compares Euler polynomials at
corresponding finite places when the tower's bottom and top fields are
identified with `D` and `L`. The field universes are zero because the number
fields used for this transport are in `Type`.

In the reduction, `D` is totally complex because it extends the CM field `E`.
The tower fields are also totally complex, so the reduction needs only the
totally complex forms of B6 and Arthur–Clozel III.4.2(c). It builds chains of
weak base changes ending at Hecke families, whose local components at the
unique place of `L` above the auxiliary place differ by Harris's condition
(4.12) for distinct double cosets. The totally complex B6 comparison gives
non-isomorphic local components of the two starting constituents.

Neither totally complex base-change premise is proved here. The rigidity
premise, prime cyclic hypothesis on `D/E`, and count of Mackey classes remain
in the target but are not used by the reduction.
