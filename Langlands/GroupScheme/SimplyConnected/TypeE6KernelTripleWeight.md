# The triple of the first actual E6 weight and its kernel restriction

For an actual index `d : TitsIndexData G` of a simply connected group and a
numbering `e : d.Vertex ≃ Fin 6`, `e6TripleFirstWeight` is three times the
actual integral fundamental character at `e.symm 0`. The triple is
dominant for the original absolute pinning because its pairings with simple
coroots are three times the nonnegative pairings of the fundamental
character. When the full star action fixes every vertex, the full star
action also fixes the triple by covariance of the fundamental characters.

If all ordered Cartan entries agree with `CartanMatrix.E 6` under `e`,
`e6TripleFirstWeight_mem_rootSpan` places this triple in the integral root
span. The proof compares the actual fundamental character with the first
weight of `TypeANegationWeyl` by their pairings with all simple coroots.
It then applies the published `three_zsmul_firstWeight` identity and checks
that each summand belongs to the integral root span.

When exactly vertex 1 is distinguished, the published E6 weight
comparison identifies the restriction of that first weight to the actual
anisotropic kernel with the first weight of the induced A5 numbering.
Linearity of restriction gives `weightRestriction_e6TripleFirstWeight`.
Both characters live on the actual maximal tori over the original
separable closure.

The weight calculation is an internal consequence of the published
E6 integral identity and actual kernel torus comparison over arbitrary
fields. The algebra module `DivisionBrauerClass` supplies the degree-six
nonvanishing used in the Brauer obstruction argument.
