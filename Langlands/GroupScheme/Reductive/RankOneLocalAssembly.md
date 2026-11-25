# Root cells in semisimple rank one from local line data

Setting: `k` is an algebraically closed field, `G` is a connected reductive group over
`Spec k`, `T` is a split torus, and `i : T ⟶ G` is a maximal torus. Any two actual roots of
`i` are integrally dependent.

## `exists_weylPoint`

For a root `α` there are a `k`-point `n` of `G` and an automorphism `σ` of `T` with these
properties:

- `n` normalizes `i` through `σ`, that is, `IsNormalizingPoint i n σ`;
- for every root `β`, `σ.hom ≫ β = -β` and `-β` is again a root.

Proof:

1. `exists_proper_isBorelPair_of_relativeRoot` gives a Borel subgroup `B ⊇ T` with
   `B ≠ G`.
2. `solvableMaximalTorusConjugacy` gives conjugacy of maximal tori in `B`.
3. `IsBorelSubgroup.properQuotientData_of_solvableProperFixedPoint` with
   `solvableProperFixedPoint` gives a smooth proper quotient `G → G/B`.
4. `nonidentityNormalizerOfRootedSolvableQuotient` gives a normalizing point `n` whose Weyl
   class is not the identity.
5. `IsConnectedReductive.weylAction_eq_neg_of_rankOne` shows that the Weyl action of `n` is
   `σ⁻¹^* β = -β` on roots. Composing with `σ.hom` gives `σ.hom ≫ β = -β`.
6. `weylAction_mapsTo_relativeRoots` shows that `-β` is a root.

The Library proof of `RootReducedness.neg_mem_roots_of_rankOne_algClosed` uses the same chain.

## `exists_latticePairing_pos`

A nonzero character of a split torus pairs positively with some cocharacter. The pairing is
perfect, and replacing `ν` by `-ν` flips the sign.

## `eq_or_eq_neg_of_mem_roots`

Suppose `α` is a root with `⟨α, ν⟩ > 0`, the only root positive on `ν` is `α`, and the only
root negative on `ν` is `-α`. Then every root `β` equals `α` or `-α`.

Proof: if `⟨β, ν⟩ = 0`, take an integral relation `m α + l β = 0` that is not the trivial
one. Pairing it with `ν` gives `m = 0`. Then `l ≠ 0`, and `l β = 0` in the torsion-free
character lattice, which contradicts `β ≠ 0`.

## `exists_isRootCell`

Hypotheses:

- `α` is a root and `⟨α, ν⟩ > 0`;
- the only root positive on `ν` is `α`, and the only root negative on `ν` is `-α`;
- the weight spaces of `α` and `-α` are lines.

Conclusion: there are a cocharacter `h` with `⟨α, h⟩ = 2` and homomorphisms
`xp xm : 𝔾ₐ ⟶ G` with `RootCell.IsRootCell i α h xp xm`.

Proof:

1. `exists_weylPoint` gives `n` and `σ`, and also `-α ∈ roots i`.
2. `rankOne_centralizer_isRepresentedBy`, applied to the Library proof
   `dynamicCentralizerReductive`, shows that the dynamic centralizer of `ν` is represented
   by `i`. No root vanishes on `ν`.
3. `RankOneLocalCell.exists_cell` gives the root groups and the open triple cell. These form
   a `RankOneRootCellRelation.CellData`.
4. `RankOneLocalRootCell.exists_isRootCell` gives `h` and the rescaled negative root group.

This file is internal to the rank-one SL2-cover development. Its local
hypotheses (positive-root uniqueness on `ν` and the root lines) are stated for the given
`G` and `ν`. It does not use the published statements `RankOnePositiveRootUniquenessStatement`
or `SplitRootLieLineStatement`.
