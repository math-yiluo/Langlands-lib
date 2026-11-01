# Arithmetic transport of the actual additive adele quotient

Worker 2. This is an internal construction from the published full adele
arithmetic equivalence and the existing quotient `AdeleQuotient K = Adeles K / K`.
It introduces no original-literature identification or existence assumption.

For number fields `K : Type uK` and `L : Type uL` in independent universes,
`map_principalAdeles` identifies the image of the actual principal additive
subgroup under `AdelicFunctoriality.adeleEquiv e`. Its forward direction uses
diagonal covariance, and its reverse direction uses `e.symm` on a rational lift.

`AdeleQuotientTransport.quotientEquiv e` is the induced continuous additive
equivalence on the actual quotient groups. Continuity in both directions
follows by composition with the quotient maps and the published forward and
inverse continuity of the adele equivalence. The two `mk` formulas describe
its value on every adelic representative. The identity, covariant composition
and inverse laws are proved on representatives or by the equivalence laws.
No compactness, Hausdorffness or measurable-space instance is assumed or added.
