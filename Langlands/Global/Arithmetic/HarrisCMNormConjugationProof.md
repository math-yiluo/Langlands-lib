# The idele-class norm commutes with arithmetic CM conjugation

`Langlands.Global.Harris.cmNormConjugation` proves
`Langlands.Global.Harris.CMNormConjugationStatement` for an algebra
embedding of CM number fields `E` into `E'` in independent universes.
This identity supplies the norm compatibility used to preserve conjugate
inversion when pulling back the correcting character in the Harris
Proposition 4.8 parity argument.
[Published statement](HarrisParityArithmeticTransportStatement.md),
[parity correction](../../../notes/harris/proposition-48-parity-transport.md)

For a place `q` of `E'` above a place `p` of `E`, let `q'` and `p'`
be their pullbacks under arithmetic conjugation. The conjugation
equivalences carry the completions at `q'` and `p'` to the completions
at `q` and `p`. The two composites from the completion at `p'` to
the completion at `q` are continuous and agree on the dense image of
`E` by `HarrisDatum.complexConj_algebraMap`. This gives a commuting square
with the actual completed field inclusions at finite and infinite
places. `Algebra.norm_eq_of_equiv_equiv` then transports each local norm
through the two conjugation equivalences.

At finite places, `HarrisDatum.conjPlace_liesOver` and the involutivity
of conjugation identify the places above `p` with those above `p'`.
At infinite places, arithmetic conjugation fixes the places and the
proof uses the induced equivalence of the corresponding subtypes. In
each adele coordinate, `Fintype.prod_equiv` reindexes the local norm
product along the place equivalence, and `map_prod` collects the
transported factors under the lower completion equivalence.

The resulting adelic equality gives the equality on idele units by
`Units.ext`. Quotient induction and the formulas for `ideleClassNorm`
and `ideleClassComplexConj` on representatives give the claimed equality
in the quotient by principal ideles.
