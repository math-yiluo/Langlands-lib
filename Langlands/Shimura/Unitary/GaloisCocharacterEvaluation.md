# Galois cocharacter evaluation

`complexCocharacterGaloisEvaluation` proves the named target
`CentralSimpleUnitaryData.ComplexCocharacterGaloisEvaluation` for every actual
central simple unitary datum `D`, with the field and scalar-tower hypotheses of
that target. It applies to every rational algebra automorphism `s` of the complex
numbers, every complex scheme cocharacter `χ` of the iterated complex group
model, and every complex unit `u`.

The first helper theorem, `complexCocharacterValue_galois`, proves that evaluation
of the transported cocharacter at `u` is the Galois point action of `s` on the
original cocharacter evaluated at `s⁻¹(u)`. The proof composes three equalities:

1. `complexCocharacterValue_galois_comparison` moves transported evaluation
   from the iterated group model to direct rational-to-complex base change.
2. `directComplexCocharacterValue_transport` applies the affine cocharacter
   transport formula in that direct model.
3. Congruence under `complexPointGaloisAction s`, applied to the reverse of
   `complexCocharacterValue_comparison` at `s⁻¹(u)`, returns to evaluation in
   the named iterated model.

The third equality is used explicitly so that the proof does not depend on an
expensive implicit conversion between the concrete models.

`complexCocharacterValue_galois_coordinates` applies the rational affine-point
coordinate equivalence to that equality, then uses
`complexPointGaloisAction_coordinates`. Its result is the equality of the full
scalar-extended similitude coordinates with coefficient action by `s`; it
compares the algebra unit as well as its multiplier.

The final theorem introduces `s`, `χ` and `u` and pairs these two helper
identities, proving precisely the conjunction in the named target. It proves
no additional matrix-chart, conjugacy-stabilizer or geometric descent claim.
