# Distinct-weight centralizers in the general linear group

This helper module implements the matrix step for the generic-centralizer
part of `GeneralLinearRationalStatement`. Its lemmas retain the explicit
diagonal-image and weight hypotheses; `GeneralLinearGenericCentralizer`
supplies these from the actual diagonal-torus and relative-root interfaces.
This module does not prove the full statement.

For an injective integral weight function `e`, the defining entry condition of
`GeneralLinear.blockLeviSubgroup` is equivalent to `Matrix.IsDiag`.
The equivalence also holds for the subgroup functor `GeneralLinear.blockLevi`
on every test scheme over `Spec R`, for any commutative ring `R`.

If a commutative group-scheme homomorphism `i` into `GL_n` has diagonal image on
every test scheme, the distinct-weight block Levi lies in `torusCentralizer i`.
The proof restricts a block-Levi point along an arbitrary refinement, transports
the product through `GeneralLinear.pointsEquiv`, and uses the commutation of
diagonal matrices. Thus it proves the all-test-scheme centralizer assertion,
including over rings with nilpotents and over nonaffine test schemes.

The final lemma assumes a factorization `λ ≫ i = diagonalCocharacter n R e`
and the dynamic block-Levi equality for that diagonal cocharacter. The preceding
inclusion and `torusCentralizer_le_dynamicCentralizer` then give
`Dynamic.centralizer (λ ≫ i) = torusCentralizer i`. The dynamic block-Levi
equality is an explicit hypothesis, to be supplied by the published proof of
`GeneralLinear.DynamicStatement`; the lemma does not assert it independently.

## Provenance

This is a derived matrix reformulation of the torus-centralizer identification
in Borel–Tits, *Groupes réductifs* (1965), Theorem 4.15(a), printed pp.90–91
(PDF pages 37–38), and Milne, *Algebraic Groups* (2017), Theorem 25.6(b) and
its proof, printed pp.545–546 (PDF pages 561–562). The all-ring version and
the diagonal-image hypothesis are internal generalizations of this matrix step.
The implementation uses the Library's dynamic subgroup and general linear
interfaces and Mathlib's `Matrix.IsDiag.diagonal_diag` and
`Matrix.commute_diagonal`; it does not claim a proof of the general reductive
generic-centralizer theorem.
