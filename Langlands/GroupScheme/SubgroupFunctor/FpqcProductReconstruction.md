# Reconstructing subgroup maps from fpqc product factorizations

Worker 680.

This internal construction supplies the descent argument used in the uniqueness
clauses of the derived-group correspondence. It uses the published
[`SubgroupFunctor.FpqcDescent`](FpqcDescent.md) and
[`Rational.SplitTorusFactorization`](../Rational/SplitTorusFactorization.md),
and the represented-subgroup factor construction in
[`Rational.LeviFactorization`](../Rational/LeviFactorization.md).
It imposes no field, reducedness, smoothness or reductivity condition.

Let `a : A ⟶ G` and `b : B ⟶ G` have commuting values, and suppose their
product factors as `e ≫ i`, where `e : A ⊗ B ⟶ P` has an effective
epimorphism of underlying schemes. Let `j : Q ⟶ G` be a monomorphism of
schemes over the base. Then `range i ≤ range j` is equivalent to
containment of both `range a` and `range b` in `range j`.
`factorOfFpqcProduct` constructs the corresponding homomorphism `P ⟶ Q`.
Its composite with `j` is `i`.

`range_eq_of_fpqc_products` compares two such factorizations with monic
target embeddings and the same first factor. If their second factors have
the same pointwise range, the target embeddings also have the same range.
The two source maps must both have effective-epimorphic underlying scheme
maps. The proof applies the containment criterion in both directions.

The proof first tests containment of `i` on the universal point of `P`.
After precomposition by `e`, this point belongs to `Q`; the published
effective-epimorphism descent theorem descends it. Every other point
follows by restriction. Containment of a product is equivalent to
containment of its factors: one implication uses the two product
inclusions, and the other uses closure under multiplication. Finally,
the representing monomorphism supplies the actual group homomorphism.

This does not identify the pointwise range of an effective epimorphism
with the entire target functor. It descends containment in a represented
monic subgroup. Finite flat surjections satisfy the effective-epimorphism
hypothesis, so the construction applies to the isogeny factorizations
in the correspondence.
