# The singleton semigroup ordered product

This internal unit derives the one-block case of the existing
`SemigroupOrderedProductStatement` from the actual constructions in
`WeightSemigroup`, the universal property in `SemigroupClosure`, and the
all-test coordinate criterion in `OrderedProductPoints`. It uses no
external structural theorem.

`singletonOrderedProductIso G` is an isomorphism of schemes over an
arbitrary base. Its forward morphism is exactly the published
`orderedMultiplication` for the constant `Fin 1` family with identity
inclusions. On every test scheme, `orderedPoints` is evaluation at the
sole coordinate. Evaluation is injective because every index equals zero,
and surjective because the constant family lifts any point. The all-test
Yoneda criterion therefore gives the isomorphism. The definition packages
that morphism and its inverse; `singletonOrderedProductIso_hom` records
the exact forward map.

For a smooth connected affine ambient group, if a semigroup contains
every ambient action weight, the total subgroup functor is an admissible
generator: it is represented by the identity of the ambient group,
which is a closed immersion, and stability is automatic. Every other
generator is contained in the total functor. The existing maximal
generator lemma then proves `semigroupSubgroup_eq_top_of_support`.
This equality holds on every test scheme.

If `Ψ : Fin 1 → Set (characterLattice S)` covers the actual ambient
support, each occurring weight lies in the sole block, hence in its
positive additive closure. `semigroupSubgroup_singleton_eq_top` applies
the preceding equality. `semigroupOrderedProduct_singleton` chooses
the ambient group for the sole representative and its identity for the
inclusion. This gives the exact realization and scheme-isomorphism
conclusion of the existing ordered-product target for one block.

The result holds over every field universe, without solvability or
splitness assumptions. Distinct-block disjointness and cross-exclusion
are vacuous in the singleton case and are not needed as hypotheses.
Zero is retained whenever it occurs; the semigroup closure does not
insert zero by a monoid convention. This unit does not prove the empty
case or the conclusion for two or more blocks.
