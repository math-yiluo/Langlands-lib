# Parameter-side premises of assembled pair L-factor inheritance

Authors: Worker 1716 (the proofs of `arithmeticPairLDirectSum` and
`arithmeticBlockPairLFactor`) and Worker 1706.

The reduction of `Langlands.Correspondence.AssemblyLInheritanceStatement` has two
premises that concern only arithmetic pair L-factors of local Weil-Deligne
representations. This module proves both of them. Their definitions are in
`AssemblyLReduction` and `AssemblyLSegmentReduction`. The proofs specialize two
general theorems of the modules `Langlands.LocalFactor.WeilDeligneEulerSum` and
`Langlands.LocalFactor.WeilDeligneBlockPair` (Worker 1716). Those theorems hold
for Weil-Deligne representations over an arbitrary field and group.

**The target statement is still not proved here.** The final theorem keeps two
hypotheses: JPSS (9.5) for square-integrable data and Henniart's segment-head
L formula.

All declarations are in namespace `Langlands.Correspondence`. Throughout,
`F : PadicField.{uF} p` and `[Fact p.Prime]`. The arithmetic pair L-factor
`arithmeticPairLFactor F` is the pair L-factor `pairLFactorClass` taken with the
inertia subgroup `Weil.Local.localInertia F` and the geometric Frobenius
`Weil.Local.localGeometricFrobenius F`.

## Theorems

### `arithmeticPairLDirectSum : ArithmeticPairLDirectSum.{uF, uP} F`

Suppose `directSum B ≃ A` and `directSum B' ≃ A'` for finite families `B`, `B'` of
local Weil-Deligne representations. Then the arithmetic pair L-factor of the
classes of `A` and `A'` is `∏ i, ∏ j` of the arithmetic pair L-factors of
`B i` and `B' j`.

Proof: take the two equivalences out of the `Nonempty` hypotheses. Then apply
`LocalFactor.WeilDeligne.pairLFactor_eq_prod_of_equiv_directSum` with the local
inertia subgroup and the geometric Frobenius. That theorem rewrites `A` and `A'`
into the direct sums (pair L-factors are invariant under equivalence). Then it
expands the pair L-factor of two direct sums as the double product.

### `arithmeticBlockPairLFactor : ArithmeticBlockPairLFactor.{uF, uP} F`

Let `ω` be the norm character of the Weil group. For local Weil representations
`B` and `B'` and `a, b : ℕ`, the arithmetic pair L-factor of the uncentered special
blocks `B ⊗ Sp(a + 1)` and `B' ⊗ Sp(b + 1)` is the product, over
`0 ≤ j < min(a + 1, b + 1)`, of the arithmetic pair L-factors of the zero-monodromy
representations `ω^(a+b-j) B` and `B'`.

Proof: apply `LocalFactor.WeilDeligne.pairLFactor_block_block` with
`ν = ω` (as a monoid homomorphism), the local inertia subgroup and the geometric
Frobenius. The hypothesis `∀ i ∈ I, ν i = 1` of that theorem is the Library's
`Weil.Local.localNormCharacter_on_inertia F`. The equation matches the premise
definitionally.

### `assemblyLInheritance_of_rankinSelberg`

```lean
theorem assemblyLInheritance_of_rankinSelberg
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F
```

This is `assemblyLInheritance_of_rankinSelberg_of_blockPairs` (module
`AssemblyLDatumExistence`) with the two theorems above as its premises `hD` and
`hB`. The two remaining hypotheses are Library statements whose proofs are not yet
in the Library:

- `SquareIntegrableDataLFactorStatement`: JPSS (9.5), the L-factor of a pair of
  Langlands quotients of square-integrable data is the product of the L-factors
  of the pairs of blocks;
- `SegmentHeadLFactorStatement`: the L-factor of a pair of segment heads,
  Henniart 2002, §2.6.

## Provenance

The module is derived. It contains no new literature claim. The direct-sum theorem
is the arithmetic counterpart of the product formula of Henniart 2002, §2.8
(printed p.596, PDF p.10). The block-pair theorem is the arithmetic L-factor
formula of Henniart 2002, §2.4 (printed p.594, PDF p.8). Both are proved here by
specializing general Weil-Deligne theorems; no literature statement is assumed.
