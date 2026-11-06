# Flattening actual unitary inducing parameters

Author: Worker 1431.

This is a derived finite assembly construction for the actual parameters in
`UnitaryGenericStatement`. It supplies concatenated parameters, an actual
normalized-induction isomorphism, and preservation of parameter validity. It
does not supply the classification data required by `UnitaryGenericExhaustion`.

For an outer positive block shape `B` of total rank `n`, let `S j` be a positive
block shape of rank `B.size j`. The canonical ordered equivalence
`e = B.flattenBlockEquiv S` identifies pairs `(j,k)` of outer and inner block
indices with the block indices of `B.flatten S`. The definitions
`flattenedUnitaryBlocks` and `flattenedUnitaryExponents` assign

`δ_flat(i) = δ((e.symm i).1)((e.symm i).2)` and
`s_flat(i) = s((e.symm i).1)((e.symm i).2)`.

The flattened ranks are definitionally the ranks of these selected inner
blocks. The shape already proves positivity and summation to `n`; no additional
rank or nonempty-family assumption is imposed. The construction works also for
any empty families permitted by the block-shape definitions.

`flattenedUnitaryProductIso` is an isomorphism from the actual twisted product
for these flattened parameters to the normalized outer product of the inner
twisted products:

`twistedProductInduced (B.flatten S) δ_flat s_flat ≅`
`normalizedProductInductionFunctor B | (j ↦ twistedProductInduced (S j) (δ j) (s j))`.

The notation on the second line describes the functor applied to that family;
the Lean conclusion uses its actual `.obj`. All products are the existing
normalized upper-block inductions, with their actual smooth complex carriers,
topologies, and actions. Field universe `uF` and representation parameter
universe `uV` remain independent, and carriers lie in `Type (max uF uV)`.
No irreducibility, unitarity, square-integrability, or exponent bound is needed
for this isomorphism.

The implementation applies the published
`Parabolic.orderedProductRegrouping` to the exact ordered refinement. Its rank
comparison is `B.flatten_size_flattenBlockEquiv`; its coordinate comparison is
`B.index_index_eq_flatten`. At each inner factor,
`e.symm_apply_apply` identifies the selected actual block and exponent with the
original ones after rank transport. The private factor and inner-product
isomorphisms implement these identifications and apply the inner induction
functor. The outer induction functor then carries their family of isomorphisms
to an isomorphism of the nested products. Composing it with regrouping proves
inhabitation of the required isomorphism type; the public definition selects
an isomorphism using classical choice. This supplies an actual map, without
asserting a canonical choice beyond the imported regrouping existence result.

`hasHermitianSymmetricParameters_flatten` assumes a multiplicity-preserving
Hermitian parameter matching for each inner family. If `ej` is its bijection,
the flattened matching sends `e(j,k)` to `e(j,ej(k))`. Thus every occurrence,
including repetitions, is retained. Local rank equality gives the flattened
rank equality; the exponent identity remains `s(i) = -s(f(i))`. The actual
isomorphism between matched blocks is the supplied local isomorphism.
The private transport lemma substitutes the index equalities and uses proof
irrelevance to reconcile the proofs of rank equality. The conclusion matches
the same unitary block at the opposite exponent, as required by the existing
Hermitian parameter predicate.

`isUnitaryGenericDatum_flatten` additionally assumes that each local family is
valid. The selected block keeps its irreducibility, invariant positive Hermitian
form, and analytic square-integrability proofs unchanged. Its exponent keeps
both strict inequalities `-1/2 < s(i) < 1/2`. Combining these with the matching
just constructed gives exactly `IsUnitaryGenericDatum` for the flattened
family.

The provenance is internal and derived: these are reindexing and functorial
composition consequences of the published ordered regrouping theorem and the
published unitary parameter definitions. No additional assertion from the
classification literature is introduced here. In particular, the construction
assumes local valid parameters; it proves neither their existence for an
arbitrary unitary generic representation nor any parameter uniqueness theorem.
