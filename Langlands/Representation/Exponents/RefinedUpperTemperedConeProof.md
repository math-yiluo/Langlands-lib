# Closed upper cones for actual tempered product-Levi exponents

Authors: Workers 526, 359 and 544. Worker 526 implemented the analytic-to-coordinate
adapter and the exact statement wrapper. Worker 359 supplied the scope and
fine-size-division guidance. Worker 544 adapted the proof documentation and
checked the exact interface. The imported analytic and coordinate theorems
retain their published authorship. This is an internal proof assembly, with
no new external source claim.

`Langlands.Exponents.refinedUpperTemperedCone.{uF,uV}` proves the exact public
[`Langlands.Exponents.RefinedUpperTemperedConeStatement`](RefinedUpperTemperedConeStatement.md).
The field and actual
representation carrier have independent universes. The theorem retains every
rank and positive ordered block shape, one Borel Haar measure on the full
central quotient, and the actual analytically tempered representation. No
irreducibility or open-character-kernel premise is introduced.

The helper theorems are in `Langlands.Exponents.RefinedUpperTemperedCone`.
Their occurrence predicate is the actual common-power generalized upper
normalized refined Jacquet scalar character, pulled back along the forward
flattened Levi equivalence and block-scalar map. The upper action is the
inverse positive half of the refined modulus on the upper-radical coinvariant
quotient. The supplied real part uses the existing residue-normalized absolute
value. No scalar eigenspace, semisimplification or chosen real part replaces
these objects.

Write `x_j(l) = x (C.flattenBlockEquiv D ⟨j,l⟩)` and let `S_j(k)` be its
partial sum over fine blocks of index below `k`. The actual nested tuple
`testScalars T C D j k e` has the uniformizer unit to the integer power `e`
on those fine blocks of original block `j`, and is one elsewhere. Its
flattened tuple is `flatScalars C D (testScalars T C D j k e)`. The supplied
real-part identity, with `q = T.residueCardinality`, gives

```text
‖ψ(flatScalars C D (testScalars T C D j k e))‖ = q ^ (-e * S_j(k)).
```

This is the public
[`RefinedUpperSquareIntegrableCone.norm_testScalars`](RefinedUpperSquareIntegrableCone.md),
which combines the real-part pairing formula with
`ProductLeviNecessity.sum_centreHMap_testScalars`. It assumes only the supplied
real part, so it applies here without square-integrability.

`partialSum_nonneg` applies the public
`ProductLeviNecessity.norm_le_one_of_diagonal` to the prefix test tuple with
uniformizer exponent one. The public test-tuple contraction, matrix and modulus
identities discharge its hypotheses: the block matrix is the uniformizer on
`testSet C D j k` and one on its complement, and the full refined modulus is
`q ^ (-|testSet| * |testSetᶜ|)`. The identity above turns the norm bound into
`q ^ (-S_j(k)) ≤ 1 = q ^ 0`. Since `q > 1`, monotonicity in the real exponent
gives `-S_j(k) ≤ 0`, hence `S_j(k) ≥ 0`. This works for every natural cut,
including zero and the full length; no nonempty proper-prefix premise is
needed by the analytic helper.

`blockSum_eq_zero` uses this nonnegative full sum and the inverse full central
test tuple, with `k = (D j).length` and `e = -1`. All fine scalars in block
`j` are the inverse uniformizer, so the tuple remains weakly contracting,
its block-scalar element is central in the original product Levi, and its
refined modulus is one. The public
`ProductLeviNecessity.norm_le_one_of_mem_center` gives norm at most one on
that tuple. The test identity becomes `q ^ S_j((D j).length) ≤ q ^ 0`,
so the full sum is nonpositive. The proof identifies this full partial sum
with `∑ l, x_j(l)` and combines the two inequalities to obtain zero
separately in every original block.
`isClosedPositiveRootCone` combines that zero total with the proper prefix
inequalities. The analytic necessity helpers are published work of Workers
819 and 219 in
[`ProductLeviTemperedExponentNecessityProof`](../Classification/ProductLeviTemperedExponentNecessityProof.md);
the real-part test identity is published work of Worker 953.

`diagonalized_isClosedPositiveRootCone` divides each scalar coordinate by the
positive size `d_l = (D j).size l` of its fine block and repeats that
determinant slope on its actual diagonal coordinates. Positivity makes
`(d_l : ℝ) ≠ 0`, so `d_l * (x_j(l) / d_l) = x_j(l)`. Thus the size-weighted
vector required by the public
[`Exponents.diagonal_cone_of_weighted_block_cone`](WeightedBlockCone.md)
is exactly the scalar vector already proved to lie in the closed cone.
The resulting diagonal coordinate is
`x_j(blockIndex (D j) a) / d_(blockIndex (D j) a)`, with precisely the
division in the statement. The imported lifting theorem obtains every
interior diagonal prefix from the fine-block boundary prefixes; it was
adapted by Worker 1008 from Worker 429's published proof.

The final theorem pairs the scalar and diagonal conclusions with precisely
the quantifiers of the public proposition. Rank zero, one-piece refinements
and zero coordinates are retained. For a one-piece refinement the scalar
zero total forces its only coordinate, and hence its repeated slope, to
vanish; in rank zero the block conclusions are vacuous. No support, chamber,
semisimplicity, finite-dimensionality, chosen-character or exponent-existence
premise is introduced. This necessary-cone result constructs no
opposite transport, actual geometric filtration, induction exponent transfer,
identity-layer map, leading-block projector, Hom comparison or classification.
