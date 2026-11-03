# Proof of the finite exact-family length criterion

`Langlands.exactFamilyLengthBound` proves the whole proposition
`Langlands.ExactFamilyLengthBoundStatement.{uI, uG, uH, uV}`. The index,
source-group, target-group and representation-carrier universes remain
independent. The theorem introduces no parameters outside that proposition
and assumes no finite length of the source representation.

This is an internal algebraic argument about actual smooth complex
representations. It does not assert a representation-theoretic length bound
for any particular induction.

## Detection on all nonzero subquotients

The hypothesis detects irreducible subquotients of `A`. The helper
`ExactFamilyLength.detects_subquotients` extends this to every nonzero
subquotient `B` of `A`. The published theorem
`SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` supplies an
irreducible subquotient `D` of `B` without assuming finite length.
`smoothSubquotientTransitivity` makes `D` a subquotient of `A`, so some `F i`
has nonzero image on `D`. Exactness preserves the subquotient presentation
by `ExactSmoothTransport.map_isSubquotient`. A nonzero subquotient forces its
ambient representation to be nonzero, as proved in the local helper
`ExactFamilyLength.nontrivial_of_isSubquotient`. Consequently `F i B` is
nonzero. This step does not require finiteness of the index type.

## A bounded measure on invariant subspaces

For each actual subrepresentation `S` of `A`, define

```
l i S = repLength ((F i).obj (A.subrepresentation S)).representation
μ S   = ∑ i, (l i S).toNat.
```

The image of the canonical inclusion `S → A` is injective by
`ExactSmoothTransport.map_injective`. The local helper
`ExactFamilyLength.length_le_of_injective`, using
`Representation.IntertwiningMap.equivLinearMapAsModule` and
`Module.length_le_of_injective`, bounds `l i S` by `b i`. Thus every such
extended-natural length is finite and `μ S ≤ ∑ i, b i`.

For `S < T`, the proof constructs the actual representation `Q = T/S`.
`ExactFamilyLength.lower` realizes `S` inside `T`, and
`ExactFamilyLength.inclusion` is the actual inclusion intertwiner. The
helpers `inclusion_injective` and `inclusion_range`, together with the
canonical quotient map's surjectivity, verify the actual short exact
sequence. The helper `quotient_nontrivial` uses a vector of `T` outside `S`
to show that `Q` is nonzero.

Applying each exact functor and using `repLength_eq_add_of_exact` gives

```
l i T = l i S + repLength ((F i).obj Q).representation.
```

The quotient-image length is finite because it is bounded by `l i T`.
`ENat.toNat_add` therefore converts this identity into ordinary natural
addition. Every summand defining `μ` is nondecreasing. Detection supplies
an index where `F i Q` is nonzero; `repLength_pos_iff` and
`ENat.toNat_pos` make that summand strictly increase. `Finset.sum_lt_sum`
then proves that `μ` is strictly monotone.

## From chains to an actual composition series

The published theorem
`LengthCriterionProof.hasCompositionLengthAtMost_of_bound` reduces the
conclusion to bounding every finite strict chain of invariant subspaces.
For a chain indexed by `Fin (m + 1)`, induction on the index gives
`j.val ≤ μ (c j)`, since each successive value strictly increases.
At the last index this yields `m ≤ μ (c (Fin.last m)) ≤ ∑ i, b i`.
The criterion supplies an actual zero-to-full composition series with the
required number of irreducible successive quotients.

The proof includes an empty finite family: its detection hypothesis rules
out nonzero subquotients, and the same chain argument yields length zero.
It assumes neither splitting nor semisimplicity.

## Dependency boundary

The direct modules are `ExactFamilyLengthStatement`, `LengthCriterionProof`,
`ExactSmoothSubquotients`, `SubquotientAlgebraProof` and
`Category.IrreducibleSubquotientExistence`, under
`Langlands.Representation`. Their results are applied to actual invariant
subspaces, quotients, intertwiners and group-algebra composition lengths.
The argument uses no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem.

For the general reductive rank-one application, actual Jacquet exactness,
finite bounds on the images, and joint detection of all irreducible
subquotients still require proofs. Nonzeroness of the actual induction and
the final two-constituent extraction are separate steps. This theorem
alone does not prove `RationalRankOneLengthTwoStatement`.

The lower subspace construction reuses the identical public
`Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof.lower`.
