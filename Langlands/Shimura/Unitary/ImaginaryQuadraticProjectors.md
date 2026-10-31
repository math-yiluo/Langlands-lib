# Natural imaginary quadratic factor idempotents

This internal algebraic construction extends the actual tensor splitting in
`ImaginaryQuadraticTensor`. The field `L` is an imaginary quadratic CM number
field, and `K` is a characteristic-zero field containing `L`. The coefficient
rings are arbitrary commutative `K`-algebras with compatible rational scalars.

`coefficientMap` is the tensor map induced by a `K`-algebra homomorphism on the
coefficient ring and the identity on `L`. `algebraEquiv_naturality` proves that
the existing natural/conjugate algebra equivalence intertwines this map with
the product of the same coefficient map on the two coordinates. The proof
uses tensor induction, the pure-tensor evaluation formula, and preservation
of the structural `K` scalars.

`factorIdempotent` is the inverse image of `(1,0)` for `false` and `(0,1)` for
`true` under that actual algebra equivalence. The two elements are idempotent,
orthogonal, and sum to one. Every coefficient-algebra map preserves them.
These equations are proved after applying the injective splitting and
calculating in the product ring; the rings may contain nilpotents or be zero.

`factorCharacter` is the natural inclusion of `L` into the coefficient ring,
precomposed with actual CM conjugation when the Boolean is `true`.
`factorEvaluation` is the corresponding coordinate of the algebra equivalence;
on `r ⊗ t` it is `r * factorCharacter(t)`. Multiplication of any tensor-algebra
element by the corresponding idempotent equals multiplication of that
idempotent by its scalar evaluation. In particular, multiplying by `1 ⊗ t`
has the character value as its scalar. Every tensor-algebra element is the sum
of its two scalar evaluations times the two idempotents. These identities follow
by applying the injective splitting and calculating in the product ring.

These are derived algebraic constructions from the existing splitting and
tensor universal property. No module decomposition, scalar-extension factor
comparison, Lie-sheaf splitting, geometric rank or source compatibility
equivalence is asserted here.
