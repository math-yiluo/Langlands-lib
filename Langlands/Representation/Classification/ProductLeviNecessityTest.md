# Test elements for the necessity of the upper Jacquet bounds

Author: Worker 219 (module assigned and its statements fixed by Worker 819).

This module is a helper for the proof of
`Langlands.GLProductLeviTemperedExponentNecessityStatement`
(see [`ProductLeviTemperedExponentNecessityStatement`](ProductLeviTemperedExponentNecessityStatement.md)).
It proves elementary facts about the test tuples `testScalars` of
[`ProductLeviNecessityCombinatorics`](ProductLeviNecessityCombinatorics.md).
Its declarations are in the namespace `Langlands.ProductLeviNecessity`. It
involves no representation and no measure.

## Notation

`C : BlockShape n` is the outer block shape and `D : BlockRefinement C` refines
each outer block `i` into the blocks of `D i`, of sizes `n_l = (D i).size l`.
`ϖ = LocalFactor.PadicAbelian.uniformizerUnit T` is the uniformizer, `q` is the
residue cardinality `T.residueCardinality`, and `|·|` is `T.normalizedAbs`, so
`|ϖ ^ e| = q ^ (-e)`. Recall that `testScalars T C D j k e i l` is `ϖ ^ e` when
`i = j` and `l < k`, and `1` otherwise.

## Statements

- `testSet C D j k` is the set of coordinates `x : Fin (C.size j)` of the outer
  block `j` whose refined block `((D j).indexEquiv.symm x).1` has index below
  `k`.
- `testScalars_isWeaklyContracting`: for every outer block `i`, the tuple
  `testScalars T C D j k 1 i` is weakly contracting for `D i`, that is
  `|c_l / c_l'| ≤ 1` whenever `l < l'`.
- `testScalars_full_isWeaklyContracting`: the same for
  `testScalars T C D j (D j).length e i` and every integer `e`.
- `testScalars_blockScalar_same`: the block scalar matrix of
  `testScalars T C D j k 1 j` is the diagonal matrix with entry `ϖ` on
  `testSet C D j k` and `1` elsewhere.
- `testScalars_blockScalar_ne`: for `i ≠ j`, the block scalar matrix of
  `testScalars T C D j k e i` is the identity.
- `testScalars_refinedLeviModulus`: the refined Levi modulus of the flattened
  element `flattenedLeviEquiv (blockScalarLevi (flatScalars (testScalars T C D j k 1))))`
  equals `q ^ (-(|S| * |Sᶜ|))` with `S = testSet C D j k` and `Sᶜ` its
  complement in `Fin (C.size j)`.
- `testScalars_full_mem_center`: the element of `C.Levi F.Carrier` whose
  component `i` is the block scalar matrix of
  `testScalars T C D j (D j).length e i` is central. Its component `j` is the
  scalar `ϖ ^ e` and its other components are `1`.
- `testScalars_full_refinedLeviModulus`: the refined Levi modulus of the
  flattened element built from `testScalars T C D j (D j).length e` is `1`.

## Helper lemmas

- `prod_zpow_eq_zpow_sum`: `∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i` for real
  `a ≠ 0` and integer exponents.
- `isWeaklyContracting_of_abs`: if `|c_l| = q ^ (-f l)` with `f` antitone in
  `l`, then `c` is weakly contracting.
- `leviModulus_blockScalarLevi_of_abs`: if `|c_l| = q ^ (-f l)`, the Levi
  modulus of the block scalars `B.blockScalarLevi c` is
  `q ^ (-∑_{l < l'} (f l - f l') n_l n_l')`.
- `card_filter_block`: the number of coordinates of `Fin N` whose block
  satisfies a predicate `P` is `∑ l, [P l] n_l`.
- `testScalars_of_ne`, `testScalars_same`, `testScalars_full`,
  `testScalars_abs`: evaluations of `testScalars`. In particular
  `|testScalars T C D j k 1 j l| = q ^ (-[l < k])`.
- `refinedLeviBlock_test`: the refined Levi block `i` of the flattened element
  built from a nested tuple `c` is `(D i).blockScalarLevi (c i)`. This is
  `refinedLeviBlock_flattenedLeviEquiv` combined with
  `flattenedLeviProductEquiv_blockScalarLevi` and `flatScalars_apply`.
- `testSet_card`, `testSet_compl_card`: `|S| = ∑_{l < k} n_l` and
  `|Sᶜ| = ∑_{l ≥ k} n_l`, from `card_filter_block`.

## Proof

1. Weak contraction. For `i ≠ j` the tuple is constantly `1`, which is weakly
   contracting by `BlockShape.isWeaklyContracting_one`. For `i = j` the
   absolute values are `q ^ (-f l)` with `f l = [l < k]` (or `f l = e`
   constant for the full tuple). This `f` is antitone, so the ratio for
   `l < l'` is `q ^ (f l' - f l) ≤ 1` since `q > 1`
   (`isWeaklyContracting_of_abs`).
2. Block scalar matrices. `ProductLeviChamber.blockScalar_val` writes a block
   scalar as the diagonal matrix with entry `c ((D j).indexEquiv.symm x).1` at
   `x`. For `i = j` this entry is `ϖ` exactly on `testSet`. For `i ≠ j` the
   tuple is `1` and `BlockShape.blockScalar_one` applies.
3. Levi modulus of block scalars. By `T.leviModulus_apply` and
   `T.determinantNorm_scalar`, the factor for a pair `l < l'` is
   `|c_l| ^ (n_l n_l') / |c_l'| ^ (n_l' n_l) = q ^ (-(f l - f l') n_l n_l')`.
   Collecting exponents with `prod_zpow_eq_zpow_sum` gives
   `leviModulus_blockScalarLevi_of_abs`.
4. Refined modulus of a test element. `T.refinedLeviModulus_apply` gives the
   product over outer blocks `i` of the Levi modulus of the refined block `i`.
   By `refinedLeviBlock_test` this block is the block scalar of `testScalars … i`.
   For `i ≠ j` it is `1` and contributes `1`. For `i = j`, step 3 with
   `f l = [l < k]` gives the exponent `-∑_{l < l'} ([l < k] - [l' < k]) n_l n_l'`.
   The summand is `n_l n_l'` when `l < k ≤ l'` and `0` otherwise (for
   `l < l'`, `[l < k] - [l' < k]` is `1` exactly when `l < k ≤ l'`). Hence the
   exponent is `-(∑_{l < k} n_l)(∑_{l' ≥ k} n_l') = -|S| |Sᶜ|`. The proof
   expands the product with `Finset.sum_mul_sum` and compares the two double
   sums term by term, using `omega` on the indicator values.
5. Full test elements. Component `j` is the block scalar of a constant tuple,
   hence the scalar matrix `GeneralLinear.scalar (ϖ ^ e)`
   (via `blockScalar_val` and `Matrix.GeneralLinearGroup.coe_scalar`). It is
   central by `GeneralLinear.scalarToCenter`. The other components are `1`.
   `Subgroup.center_pi` turns centrality in the product group `C.Levi` into
   componentwise centrality. For the modulus, `f` is constant, so every
   exponent `(f l - f l') n_l n_l'` vanishes and the modulus is `1`.

## Provenance

These are routine computations with the modular character of a standard
parabolic subgroup of `GL_n`, evaluated on diagonal elements. For a standard
Levi with blocks of sizes `n_1, …, n_r`, the modulus at block scalars
`(c_1, …, c_r)` is `∏_{l < l'} |c_l| ^ (n_l n_l') |c_l'| ^ (-n_l n_l')`. This is
the formula of the Library's `T.leviModulus_apply`, and the module uses it
directly rather than any external source. The test tuples are internal to this
proof. They are the extremal rays used in
[`ProductLeviNecessityCombinatorics`](ProductLeviNecessityCombinatorics.md).
The statements were fixed by Worker 819 and the proofs were written by
Worker 219.
