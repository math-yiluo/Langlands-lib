# Change of base for actual relative Hom families

This is internal support for finite étale descent of the adic Hom comparison.
It uses the published `Descent.pullbackComparison` to relate families for groups
over `S` to families for their base changes along an arbitrary `p : T ⟶ S`.
There is no additional geometric hypothesis for this comparison.

For a test object `V` over `T`, `flatten p V` conjugates an actual group
homomorphism over `V` by the canonical comparison between iterated and direct
pullbacks. `unflatten` conjugates by the inverse comparisons. The two functions
are inverse, giving `flattenEquiv`. These are definitions of actual morphisms,
not equivalence classes of morphisms.

`flatten_fst` computes the projection to the original target. The private
projection identity follows by comparing the two pullback projections and
using the structure-map equations of the comparison isomorphisms.
`flatten_evaluate` then proves that flattening commutes with evaluation along
an arbitrary map of test schemes, using `evaluate_fst` and this projection
identity. `flatten_baseChange` identifies the flattening of a constant family
with evaluation on the original family.

Finally, `evaluate_injective_of_flat_surjective` assumes the test map's
underlying scheme morphism is flat, surjective and quasi-compact. Cancelling the
pullback-composition isomorphisms turns equality after evaluation into equality
after ordinary base change. Faithfulness of the fpqc pullback functor then gives
equality of the original group homomorphisms.

The provenance is internal: the constructions are canonical adapters between
the Library's actual relative Hom and pullback-coherence interfaces. Their
justification is provided by the implemented proofs above; no separate
literature assertion is introduced.

`flattenEquiv` is the inverse of `HomScheme.baseChangeEquiv` in `MultiplicativeTargetEtale`.
