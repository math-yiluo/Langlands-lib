# Transport of an actual Jordan–Hölder series along an equivalence: proof

Author: Worker 244.

`Langlands.jordanHolderSeriesTransport` proves exactly the published
`JordanHolderSeriesTransportStatement.{uK, uG, uA, uB}` from
`Langlands.Representation.Filtration.JordanHolderStatement`. The field `k`, the
monoid `G`, and the carriers of `A : Rep.{uA} k G` and `B : Rep.{uB} k G` keep
four independent universes. Fix an equivalence of representations
`φ : A.ρ.Equiv B.ρ`, a length `n`, and a supplied filtration
`s : ObjectRepFiltration A n` with `s.HasSimpleFactors`. The theorem produces
`t : ObjectRepFiltration B n` with `t.HasSimpleFactors` and, for every
`i : Fin n`, an actual `Representation.Equiv` from
`(s.gradedRepresentation i).ρ` to `(t.gradedRepresentation i).ρ` at the same
index.

There are no further hypotheses: no finite-dimensionality, global finite
length, nontriviality, or group structure. The case `n = 0` is covered by the
same construction. The statement pair and every pair it imports are unchanged.
This pair proves only the transport component. Comparison of two series,
transitivity, and assembly of `JordanHolderSeriesStatement` are separate proof
work. The helpers below are in the namespace
`Langlands.JordanHolderTransportProof`.

## Images of invariant subspaces

`equiv_apply_rep` restates the intertwining law of `φ` pointwise:
`φ (A.ρ g v) = B.ρ g (φ v)`. `mapSub φ S` is the image of an invariant subspace
`S` of `A.ρ` under the underlying linear equivalence of `φ`. It is invariant
because the image of `A.ρ g v` is `B.ρ g (φ v)`. `mem_mapSub_iff` uses
Mathlib's `Submodule.mem_map_equiv`: a vector `w` lies in `mapSub φ S` exactly
when `φ⁻¹ w` lies in `S`.

`subrepOrderIso φ` is an order isomorphism from the lattice of invariant
subspaces of `A.ρ` to that of `B.ρ`. Its forward map is `mapSub φ`. Its inverse
is `mapSub φ.symm`. The two composites are identities by `mem_mapSub_iff` and
cancellation of `φ` with its inverse. Images preserve and reflect inclusion,
again by `mem_mapSub_iff`.

## Equivariant isomorphisms of successive quotients

The proof reuses `LengthCriterionProof.lower` and `LengthCriterionProof.quotientRep`
from the published `Langlands.Representation.Filtration.LengthCriterionProof`.
For invariant subspaces `S` and `T`, `quotientRep S T` is the action on the
quotient of `T` by `S` pulled back to `T`. For consecutive steps of an
`ObjectRepFiltration`, this action is definitionally the action of the graded
representation at that index.

`upperEquiv φ T` is Mathlib's `LinearEquiv.submoduleMap`. It is the
restriction of `φ` to a linear equivalence from `T` to `mapSub φ T`.
`map_lower` proves that it carries `lower S T` onto
`lower (mapSub φ S) (mapSub φ T)`. Both memberships reduce, through
`Submodule.mem_map_equiv` and `mem_mapSub_iff`, to the same condition: the
inverse image of the vector lies in `S`.

`quotientEquiv φ S T` is the induced linear equivalence of quotients,
`Submodule.Quotient.equiv`, packaged as a `Representation.Equiv` from
`quotientRep S T` to `quotientRep (mapSub φ S) (mapSub φ T)`. For equivariance,
`Submodule.linearMap_qext` and `LinearMap.ext` reduce the claim to the class of
one vector `x ∈ T`. Both sides are the classes of elements of `mapSub φ T`
whose underlying vectors are `φ (A.ρ g x)` and `B.ρ g (φ x)`. These agree by
`equiv_apply_rep`. The construction does not use `S ≤ T`.

## The transported series

The main theorem defines `t` by `ObjectRepFiltration.ofSubrepresentations`. Its
`i`th step is the image `subrepOrderIso φ (s.subrepresentation i)`. Its steps are
monotone because the order isomorphism and the steps of `s` are monotone. The
endpoint laws come from those of `s` and from `OrderIso.map_bot` and
`OrderIso.map_top`. By construction, the steps of `t` are definitionally these
images.

For simple factors, the proof uses the published
`LengthCriterionProof.hasSimpleFactors_iff_covBy`: a filtration has simple
factors exactly when each step is covered by the next. The covering relations
for `s` transfer to `t` by `apply_covBy_apply_iff`, because order isomorphisms
preserve covering. At index `i`, the required equivalence of graded quotients is
`quotientEquiv φ` applied to `s.subrepresentation i.castSucc` and
`s.subrepresentation i.succ`. Its codomain is definitionally
`(t.gradedRepresentation i).ρ`. No index permutation is needed.

## Provenance and scope

This is derived general module theory for representations of an arbitrary
monoid over a field. It is the elementary fact that an isomorphism carries a
composition series to a composition series with isomorphic factors. The
motivation and literature locators, from BZ77, are documented in the imported
`JordanHolderStatement.md`. The arbitrary-field, arbitrary-monoid formulation is
internal, not a theorem attributed verbatim to BZ77. The proof uses only
`propext`, `Classical.choice`, and `Quot.sound`. It contains no proof hole and
no new axiom.
