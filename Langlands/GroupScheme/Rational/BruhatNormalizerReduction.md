# Normalizer uniqueness from the opposite unipotent cell

This internal reduction formalizes the group calculation in Borel–Tits,
*Groupes réductifs* (1965), §§5.13 and 5.15, printed pages 99–100
(zero-based PDF pages 45–46). It uses the actual normalizer points and
dynamic unipotent subgroup functors of the Library. The inverse cocharacter
is explicitly the composite with `Gm.powerHom S (-1)`, as in the published
`OppositeCellStatement`.

`HasUnipotentWeylFactorization i ν` records the factorization of each
`u ∈ U(k)` as `a * b`, with `a,b ∈ U(k)`, such that `n⁻¹ * a * n`
belongs to `U⁻(k)` and `n⁻¹ * b * n` belongs to `U(k)`. The geometric
root-product factorization in §5.13 supplies this assertion in the source's
reductive setting; this file retains it as an explicit hypothesis.

`HasTrivialNormalizerOppositeCellIntersection i ν` says that a normalizing
point in `U⁻(k) U(k)` is the identity. The source proves this assertion in
§5.15 using uniqueness in the opposite cell and conjugation by all torus
points. This file does not assume that rational torus points detect the
whole-torus centralizer and does not prove the geometric assertion.

`hasUnipotentNormalizerSeparation_of_weylFactorization_of_oppositeCell`
proves the conditional implication from those two assertions. Given
`n' = u * n * v`, factor `u = a * b`. Then

`n⁻¹ * n' = (n⁻¹ * a * n) * ((n⁻¹ * b * n) * v)`

is a normalizing point in `U⁻(k) U(k)`, hence is the identity. Cancellation
gives `n' = n`, which is the existing `HasUnipotentNormalizerSeparation`
predicate. This proof is just group multiplication and subgroup closure;
it holds over any field, without affineness, maximality, or genericity.

For an affine group scheme,
`hasRationalBruhatDecomposition_of_weylFactorization_of_oppositeCell`
combines this implication with the preceding unipotent assembly module.
It retains the dynamic-centralizer identity, unipotent covering, root-product
factorization, and normalizer-cell intersection as hypotheses. These are
remaining proof obligations for the unchanged exact `RationalBruhatStatement`;
the conditional helper does not establish that final theorem.
