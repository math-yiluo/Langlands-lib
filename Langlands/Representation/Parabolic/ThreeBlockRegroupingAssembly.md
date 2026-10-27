# Three-block associativity from ordered product regrouping

Author: Worker 832.

This internal module shows that the general ordered regrouping proposition
`Parabolic.OrderedProductRegrouping` implies associativity of normalized
parabolic induction for three consecutive blocks. It is conditional: the
regrouping proposition is a hypothesis of every construction here. The module
does not prove `OrderedProductRegrouping`, and it does not by itself prove
`ThreeBlockInductionAssociativityStatement`.

Throughout, `T` is a topological datum of a `p`-adic field `F`, the ranks
`C`, `A`, `B` are positive, and `σ0`, `σ1`, `σ2` are bundled smooth
representations of `GL_C`, `GL_A`, `GL_B` with carriers in `Type (max uF uW)`.
The regrouping hypothesis is
`regrouping : OrderedProductRegrouping.{uF, max uF uW} F T`.

## Generic adapters

In namespace `PadicField.TopologicalData`:

- `normalizedProductInductionRankCastEquiv h B σ`: for an equality `h : m = n`
  of total ranks, the normalized product of `σ` along `B`, with the group action
  precomposed with the entry-preserving reindexing `reindex (finCongr h)`, is
  equivalent to the normalized product along `B.rankCast h.symm`. The proof is
  `subst h` followed by the identity equivalence.
- `normalizedProductInductionFamilyEqEquiv B h`: equal factor families
  `σ = σ'` give equivalent normalized products (by `subst`).
- `normalizedProductInductionObjEquiv B σ`: the representation of the functor
  value `(T.normalizedProductInductionFunctor B).obj σ` is identified with
  `T.normalizedProductInduced B (fun i => (σ i).representation)` (the identity
  equivalence; the two agree definitionally).

In namespace `Parabolic`, `equivSymm`, `equivTrans` and `equivPrecomp` are the
inverse, the composite, and the precomposition of both actions with a monoid
homomorphism, for `Representation.Equiv`. They are Mathlib's
`Representation.Equiv.symm`, `Representation.Equiv.trans` and the evident
precomposition, restated with every semiring, monoid and module structure as an
implicit argument. They are mathematically identical to the Mathlib
operations; the restatement only makes Lean read those structures off the
given equivalences instead of synthesizing them again on induced carriers.

## Pair families

- `pairSmoothFamily T σ1 σ2` is the family over `Fin 2` with values `σ1` and
  `σ2` at ranks `![a, b]`.
- `pairSmoothFamilyProductEquiv T ha hb σ1 σ2` identifies the normalized product
  along `twoBlocks a b` of that family with the product of the literal pair
  family `pairFamily σ1.representation σ2.representation`, blockwise by
  identity equivalences.

## The two regroupings

- `leftRegroupingEquiv T regrouping C A B hC hA hB σ0 σ1 σ2` is an equivalence
  from the three-block product of `threeBlockSmoothFamily σ0 σ1 σ2` along
  `threeBlocks C A B` (total rank `C + (A + B)`) to the normalized product along
  `twoBlocks C (A + B)` of `σ0` and the normalized product of `σ1`, `σ2` along
  `twoBlocks A B`. It applies the published adapter
  `normalizedProductRegroupingToEquiv`, i.e. the hypothesis `regrouping`, to the
  data `leftRefinement`, `leftLabelEquiv`, `leftLabelEquiv_size` and
  `leftLabelEquiv_index` of `ThreeBlockRefinementGeometry`. The inner products
  are identified blockwise: the first inner product, along the one-block shape
  of rank `C`, is identified with `σ0` by the published
  `singleBlockTransportedProductEquiv`; the second, along `twoBlocks A B`, is
  identified with the pair product through `pairSmoothFamilyProductEquiv`. In
  both cases the transported inner family is first rewritten by
  `normalizedProductInductionFamilyEqEquiv`, using that it equals the expected
  family definitionally on each concrete label.
- `rightRegroupingEquiv T regrouping C A B hC hA hB σ0 σ1 σ2` is the analogous
  equivalence from the product along `threeBlocksRight C A B` (total rank
  `C + A + B`) to the normalized product along `twoBlocks (C + A) B` of the
  product of `σ0`, `σ1` along `twoBlocks C A` and `σ2`. It uses
  `rightRefinement`, `rightLabelEquiv`, `rightLabelEquiv_size` and
  `rightLabelEquiv_index`; the first inner block is a two-block product and the
  second is the one-block product of rank `B`.

## Assembly

- `threeBlockRankCastEquiv` is `normalizedProductInductionRankCastEquiv` at
  `Nat.add_assoc C A B`: the three-block product along `threeBlocks`, with the
  action precomposed with `reindex (finCongr (Nat.add_assoc C A B))`, is
  equivalent to the product along `threeBlocksRight`, which is definitionally
  the rank cast of `threeBlocks`.
- `threeBlockAssociativityEquiv` composes the inverse of `leftRegroupingEquiv`
  (precomposed with the same reindexing), `threeBlockRankCastEquiv` and
  `rightRegroupingEquiv`. Its source is the left bracketing
  `σ0 × (σ1 × σ2)` with the action precomposed with the entry-preserving rank
  transport, and its target is the right bracketing `(σ0 × σ1) × σ2`.
- `commonUniverseThreeBlockAssociativity_of_regrouping` proves the published
  proposition `CommonUniverseThreeBlockAssociativity.{uF, uW}` from a regrouping
  hypothesis
  `∀ p [Fact p.Prime] (F : PadicField.{uF} p), OrderedProductRegrouping.{uF, max uF uW} F F.canonicalTopologicalData`:
  it bundles the smooth representations `τ0`, `τ1`, `τ2` with `SmoothRep.of`
  and applies `threeBlockAssociativityEquiv` at the canonical topological data.

Combined with the published `threeBlockInductionAssociativity_of_common`, a
published proof of `OrderedProductRegrouping` at carrier universe
`max uF uV0 uV1 uV2` then yields the literal heterogeneous statement.

## Provenance

Internal. The module is a composition of Library constructions: the
regrouping hypothesis through the adapter `normalizedProductRegroupingToEquiv`,
the factor equivalences of `RegroupingFactorEquivalences`, the block data of
`ThreeBlockRefinementGeometry`, and the reduction target of
`ThreeBlockUniverseReduction`. No external theorem is quoted or asserted;
every step is the Lean construction described above, and the mathematical
content of associativity is entirely carried by the regrouping hypothesis.
