# Closed upper cones for actual tempered product-Levi exponents

Authors: Workers 526, 359 and 544. Worker 526 supplied the complete statement
pair; Worker 359 supplied the scope and fine-size-division guidance; Worker 544
adapted the documentation and checked the exact interface. This pair defines
an internal proposition. The proposed result is a coordinate adapter for
already published analytic necessity bounds; its proof remains separate.

`Langlands.Exponents.RefinedUpperTemperedConeStatement.{uF,uV}`
quantifies a prime, an actual finite p-adic extension in universe `uF`,
its compatible topological data `T`, an arbitrary natural rank and an
ordered positive block shape `C`. With the supplied field topology and
product-Levi topological group installed, it quantifies one arbitrary
Borel measurable-space structure and Haar measure on the actual quotient
`C.Levi F.Carrier / center(C.Levi F.Carrier)`. The actual representation
`σ` has carrier in the independent universe `uV`, and satisfies
`IsTemperedModCenter σ μ`. This predicate supplies admissibility, a
unitary full central character and all descended smooth coefficients in
`L^(2+ε)` for every `ε > 0`. No irreducibility premise is present.

For every refinement `D` of `C`, the tuple character `ψ` is an actual
common-power generalized eigencharacter of
`T.normalizedRefinedJacquet C D σ`, restricted along the composite

```lean
(flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
  ((C.flatten D).blockScalarLevi F.Carrier)
```

The [forward flattened Levi equivalence](../Geometric/FlattenedLevi.md)
maps the flattened product Levi into the actual refined Levi subgroup.
The [refined Jacquet construction](../Geometric/RefinementFunctors.md)
is the upper-radical coinvariant quotient with the inverse positive half
of the full refined modulus: its action on a class is
`δ_D(m)^(-1/2) [σ(m) v]`.

Generalized occurrence uses the existing `IsGeneralizedEigencharacter`:
some nonzero quotient vector is killed by one common power of
`π(a) - ψ(a)` for every scalar tuple `a`. Its supplied real part `x`
satisfies exactly `T.IsRealPartOf ψ x`, namely
`‖ψ(a)‖ = ∏ i, |a_i|^(x_i)`, using
`|·| = T.normalizedAbs = q^(-valuation)` and `q = T.residueCardinality`.
The tuple character is not required separately to have open kernel.
The proposition makes no existence claim for real parts or exponents.

Write `xⱼ(l) = x (C.flattenBlockEquiv D ⟨j,l⟩)` and
`dⱼ(l) = (D j).size l`. The conclusion is the conjunction of:

- For each original block `j`, `xⱼ` is in the existing
  `IsClosedPositiveRootCone`: its total sum is zero and each proper
  prefix sum is nonnegative.
- For each original block `j`, the vector on its actual diagonal
  coordinates given by `a ↦ xⱼ(blockIndex (D j) a) /
  dⱼ(blockIndex (D j) a)` is in that same closed cone.

The division is essential: `xⱼ` is the scalar real part, while the
repeated vector consists of determinant slopes. On a fine block of size
`dⱼ(l)`, `|det(a I)| = |a|^(dⱼ(l))`, so a determinant slope `tⱼ(l)`
has scalar real part `dⱼ(l) * tⱼ(l)`. Here
`tⱼ(l) = xⱼ(l) / dⱼ(l)`. Every fine size is positive, so the
size-weighted slope is exactly `xⱼ(l)`, and repeating the slope over
the fine block gives the stated diagonal vector. This is the convention
of [`Chambers`](Chambers.md), including
`isRealPartOf_blockSize_mul_iff`.

Each original block gets its own zero total and prefix inequalities;
there is no comparison between different original blocks. Rank zero,
one-piece refinements, zero coordinates and all allowed block sizes are
retained. In rank zero the block conclusions are vacuous. In a one-piece
refinement the scalar total forces its sole coordinate to be zero, and
the diagonal vector is zero. The statement assumes no chamber,
nonvanishing Hom space, cuspidal support, finite-dimensional carrier,
semisimplicity or chosen representation equivalence.

The provenance is an internal deduction proposed from proved Library APIs:

- [`ProductLeviTemperedExponentNecessityProof`](../Classification/ProductLeviTemperedExponentNecessityProof.md),
  by Workers 819 and 219, supplies
  `Langlands.ProductLeviNecessity.norm_le_one_of_diagonal` and
  `Langlands.ProductLeviNecessity.norm_le_one_of_mem_center`. These
  helper theorems assume analytic temperedness and generalized occurrence,
  with no irreducibility, positive-rank or open-character-kernel premise.
  Their test-tuple contraction, matrix and modulus hypotheses are verified
  by the existing `ProductLeviNecessityTest` lemmas.
- [`RefinedUpperSquareIntegrableCone`](RefinedUpperSquareIntegrableCone.md),
  by Worker 953, supplies
  `Langlands.Exponents.RefinedUpperSquareIntegrableCone.norm_testScalars`.
  This identity requires only the supplied real part, despite its module's
  name. On the prefix test with uniformizer exponent `e` it gives
  `‖ψ(test)‖ = q^(-e * partialSum xⱼ k)`. The diagonal bound with
  `e = 1` gives nonnegative proper prefixes and, at the full length, a
  nonnegative total. The full inverse central test with `e = -1` and
  `norm_le_one_of_mem_center` gives a nonpositive total. Thus each
  total is zero, since `q > 1`.
- [`WeightedBlockCone`](WeightedBlockCone.md) supplies
  `Langlands.Exponents.diagonal_cone_of_weighted_block_cone`, adapted by
  Worker 1008 from Worker 429's published proof. Apply it to the fine
  shape `D j` and slopes `xⱼ(l) / dⱼ(l)`. Their size-weighted vector
  equals `xⱼ`, giving the diagonal clause.

This is an internal formulation of that route, with no new external
source claim or new temperedness criterion. The two imports of the supplied
statement are retained; the helper modules above explain the intended
derivation and are not additional imports or premises.

This statement supplies a necessary numerical cone for actual upper
refined generalized exponents. Opposite transport, geometric exponent
transfer, grade identification, whole-induction isolation, generalized-space
splitting and the parent relative Hom comparison remain separate
obligations.
