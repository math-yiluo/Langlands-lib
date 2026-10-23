# Proof of compactness of the determinant-unit central intersection

Author: Worker 225.

The target is
`Langlands.CuspidalSupport.LeviDeterminantUnitCentralCompactnessTheorem F T B`
from `Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement`.
The theorem `Langlands.CuspidalSupport.leviDeterminantUnitCentralCompactness`
proves it for every prime `p`, field `F : PadicField.{uF} p`, compatible
`T : F.TopologicalData`, rank `n` (including zero) and block shape
`B : BlockShape n`. It uses the actual topology `T.topology`, the actual
subgroup `determinantUnitSubgroup T B` and the actual group center. The
statement and all imported Library pairs are unchanged. The proof assumes no
compactness or centrality.

The statement is BZ76, Chapter II, section 3.20(a); the Lean proof is a
direct argument. A central element of the product Levi is a family of scalars. Its block determinant
norms are powers of the scalars' norms. So the intersection is a product of
copies of the norm-one units.

## Norm-one units are compact

The helper theorem `isCompact_ker_normalizedAbsUnits T` proves, under
`T.topology`, that the kernel of `T.normalizedAbsUnits : F.Carrierˣ →* ℝ≥0ˣ`
is compact.

Install the valuative relation and the `IsNonarchimedeanLocalField` structure
carried by `T`. Let `S` be the set of field elements of valuation exactly `1`
for `ValuativeRel.valuation F.Carrier`.

- `S` is closed. It is the sphere of radius `1`, closed by Mathlib's
  `Valuation.isClosed_sphere` (after `Valuation.restrict_eq_one_iff`).
- `S` lies in the closed unit ball. That ball is compact by
  `IsNonarchimedeanLocalField.isCompact_closedBall`. So `S` is compact.

The kernel is the preimage of `S` under `Units.val`. A unit `a` has
`T.normalizedAbs a = 1` exactly when `T.discreteValuation a = 1`, by the
published `normalizedAbs_eq_one_iff_discreteValuation`. By definition,
`T.discreteValuation` is `ValuativeRel.valuation` mapped through the
ordered multiplicative isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`.
That isomorphism is injective and maps `1` to `1`. So this is equivalent to
valuation `1`.

`Units.val` is an embedding (`Units.isEmbedding_val₀`), and every element of
`S` is nonzero, hence the value of a unit (`Units.mk0`). So
`IsInducing.isCompact_preimage'` transfers compactness of `S` to the
kernel.

## The intersection as a continuous image

Define `Φ : (Fin B.length → F.Carrierˣ) → B.Levi F.Carrier` by
`Φ c i = GeneralLinear.scalar (c i)`. It is continuous: each coordinate is the
continuous homomorphism `GeneralLinear.scalarContinuous` composed with
evaluation at `i`, and the Levi has the product topology.

The proof shows that the intersection, as a set, equals the image under `Φ` of
`Set.univ.pi` of the norm-one units. In other words, it equals the families of
scalars whose entries all have normalized absolute value one. The set
equality is unfolded with:

- `mem_determinantUnitSubgroup`: every block determinant norm is `1`.
- `Subgroup.center_pi` and `Subgroup.mem_pi`: the center of the product is
  the product of the block centers.
- `Matrix.GeneralLinearGroup.center_eq_range_scalar`: each block center is
  the set of invertible scalars.

Forward direction. Choose scalars `c i` with `scalar (c i) = g i`. By the
published `determinantNorm_scalar`, the determinant condition on block `i`
becomes `T.normalizedAbsUnits (c i) ^ B.size i = 1`. In the nonnegative reals,
`pow_eq_one_iff_of_nonneg` with the nonzero exponent `B.size i` (from
`B.positive i`) gives `T.normalizedAbsUnits (c i) = 1`. Then `g = Φ c`.

Reverse direction. Every `scalar (c i)` is central. Its determinant norm is
`T.normalizedAbsUnits (c i) ^ B.size i = 1 ^ B.size i = 1`.

## Conclusion

A finite product of compact sets is compact (`isCompact_univ_pi`). Its
continuous image under `Φ` is compact (`IsCompact.image`). This proves the
target.

The rank-zero case needs no separate argument. Then `Fin B.length` is empty,
the product is a single point, and the same lemmas apply.

## Source

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F), where F is a non-Archimedean local field*, Russian Mathematical
Surveys 31:3 (1976), 1–68, Chapter II, section 3.20(a), printed page 34.
Registered source ID: `bernstein-zelevinsky-1976-representations-gln`.
