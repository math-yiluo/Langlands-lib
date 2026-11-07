# Scalar-uniformizer norms order real twists of cuspidal classes

This internal construction uses the published admissible Schur lemma, actual
supercuspidal class representatives, scalar-character transport and the proved
scalar-uniformizer value of a real determinant character. It introduces no
representation-theoretic existence hypothesis beyond those published results.

For a cuspidal datum `ρ`, `scalarCharacter` chooses the scalar character of its
canonical representative. `scalarCharacter_acts` records its actual scalar
action. `scalarCharacter_eq_of_isRepresentedBy` proves that this choice agrees
with every prescribed scalar character of any actual representative of the
same class: transport that action through an isomorphism, evaluate both actions
on a nonzero vector, and cancel the vector.

`scalarUniformizerNorm` is the positive real norm of this character at the
scalar uniformizer. `scalarUniformizerNorm_pos` follows because a character
has unit values. `scalarUniformizerNorm_twist` states the exact formula
`norm(ν^s ρ) = norm(ρ) q^(-rank(ρ) s)`. The proof uses the twisted actual
representative, multiplies its scalar character by the determinant character,
and applies the existing uniformizer-value calculation. Finally,
`strictAnti_scalarUniformizerNorm_twist` uses positive rank and `q > 1` to prove
strict decrease for all real twist parameters. Thus increasing segment factors
have strictly decreasing scalar-uniformizer norms, independently of repeated
classes or equal norms elsewhere in a finite family. Field and carrier
universes are independent throughout.
