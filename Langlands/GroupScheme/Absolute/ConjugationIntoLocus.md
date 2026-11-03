# The closed locus of conjugation into a closed subgroup

Author: Worker 1438.

This internal construction uses the published universal closed-factorization
locus to construct the inverse-conjugation transporter needed in the proof of
Milne's centralizer and Borel intersection theorem.

For homomorphisms `s : H ⟶ G` and `b : B ⟶ G`, `ConjugationInto.Holds s b g`
means that on every refinement `V ⟶ T` of a test scheme, every point of `H(V)`
has its image conjugated by `g⁻¹` into the actual range of `b` on `V`. It is a
condition on all test schemes, including nonreduced ones.

The morphism `conjugationHom s` sends `(h,g)` to `g⁻¹ s(h) g`. The pullback
`productLocus s b` of the target subgroup along this map is closed in `H × G`
when `b` is closed. Testing on the universal point of `H × T` proves
`holds_iff_factors`: the condition is equivalent to the entire product map
`H × T → H × G` factoring through this pullback. The converse follows by
precomposition with each pair of test points.

Over any field, with `H` affine, the published
`ClosedFactorizationLocusProof.closedFactorizationLocus` then gives an actual
closed subscheme of `G` representing this condition. Flatness and coordinate
projectivity are automatic over a field, by the published field reductions.
`locus` and `inclusion` choose that actual subscheme and its closed immersion;
`factors_inclusion_iff` states the exact universal property.

No smoothness, finite type, connectedness, torus, or algebraic closure
hypothesis is used. The transporter need not be a subgroup and is not given a
group structure.

The construction is derived from published universal factorization and
pullback interfaces; it assumes no new geometric representability theorem.
It formalizes the closed transporter used for equation (126) in Milne,
*Algebraic Groups* (2017), Theorem 17.46, printed p.365, zero-based PDF381.
It does not prove that the product of the centralizer and a Borel is closed,
nor that the centralizer intersection is Borel.
