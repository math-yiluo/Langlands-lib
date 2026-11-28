# The original chart and the section charts

`secTrans` indexes the translations of `Y` by `Option (Sect g)`. The index
`none` uses the identity. The index `some c` uses left translation by the
section `c`. The glued scheme `Gl`, chart maps `ch`, and structure morphism
`toS` are the corresponding specialization of the construction in `Glue`.

`dom_chart` proves that on the domain of a translation, its chart agrees
with the translated point in the original chart. The proof uses the
inclusion of the original transition domain into the extended graph overlap.
The scheme-valued product formulas then express this equality as a
comparison of `ch (some c)` with multiplication by `c`. This is the relation
for `X(a)` in BLR, *Néron Models*, §5.3, pp. 122–123.
