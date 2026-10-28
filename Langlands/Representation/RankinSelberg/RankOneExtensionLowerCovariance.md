# Lower-parabolic covariance of the rank-one extension sections

Module `Langlands.Representation.RankinSelberg.RankOneExtensionLowerCovariance`.

This helper module computes how the scalar coefficient of a section of the actual
normalized lower induced model transforms under left multiplication by a lower block
`B(m, x, a) = [m, 0; x, a]` in `GL_(1+(t+1))`.

## Provenance

In Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105
(1983), Lemma 5.5 (printed pp. 424–426), the representation of `GL_(t+2)` is induced from
the lower parabolic with blocks `(t+1, 1)`. Its Whittaker functions are unfolded through
the factorization `B(m, x, a)` of the lower parabolic. The formula below is the
covariance law of that induced representation, written for the Library's actual
construction `rankOneExtensionLowerSection` / `rankOneExtensionLowerSectionCoefficient`
(published module `RankOneExtensionStableJacquetData`). It is derived for this
formalization and is not quoted from the paper.

## Contents

Algebraic part (for any field `K`):

- `rankOneExtensionLowerShape_index_val` and the imported
  `rankOneExtensionLowerBlock_entry` from
  [RankOneExtensionCellAlgebra](RankOneExtensionCellAlgebra.md) give plain
  `Fin (1 + (t + 1))` coordinates for the lower shape and the lower block.
- `rankOneExtensionLowerBlock_mem_oppositeParabolic`: `B(m, x, a)` lies in the opposite
  (lower) parabolic of `rankOneExtensionLowerShape t`. The packaged element is
  `rankOneExtensionLowerBlockParabolic m x a`.
- `oppositeLeviProjection_lowerBlock_large`: its Levi component on the large block is
  `m`.
- `oppositeLeviProjection_lowerBlock_scalar_det`: its Levi component on the scalar block
  has determinant `a`.

Tensor part:

- `piTensorProduct_comp_apply_eq_mul` is a generic extension lemma. If two linear forms
  `φ₁ ∘ A` and `c • φ₂` on a `PiTensorProduct` agree on pure tensors, they agree
  everywhere.
- `rankOneExtensionTensorContraction_tprod` evaluates the published contraction on an
  arbitrary pure tensor of the reversed carrier: `ℓ(v 0) · (v 1).down`.

p-adic part:

- `rankOneExtensionLowerShape_leviModulus`: the modulus of the lower Levi is
  `|det m| / |det a|^(t+1)`.
- `rankOneExtensionLowerSectionCoefficient_lowerBlock_mul`: for every section `f`, every
  `g`, and every `m, x, a`,

  `c_f(B(m, x, a) g) = (sqrt(|det m| / |a|^(t+1)))⁻¹ · χ(a) · C_(ℓ ∘ σ(m))(f(g))`,

  where `C_λ` is `rankOneExtensionTensorContraction λ` and `f(g)` is
  `rankOneExtensionLowerSectionEval`.

## Proof method

The parabolic membership and the Levi components are computed entrywise from the
explicit block indices (`0` for the large block, `t + 1` for the scalar block). The
coefficient formula starts from the Library's covariance law
`normalizedOppositeParabolicInduced_covariant`, applied to the parabolic element
`B(m, x, a)`. This law multiplies by the inverse square root of the Levi modulus and
applies the block tensor action. The Levi modulus is rewritten with
`rankOneExtensionLowerShape_leviModulus`. The block tensor action is identified with
`χ(a) · C_(ℓ ∘ σ(m))` by checking pure tensors only, via
`piTensorProduct_comp_apply_eq_mul`. On a pure tensor, the published
`blockTensor_tprod` acts by `σ(m)` on the large factor and by `χ(det a)` on the scalar
factor. The generic tensor lemma is stated in a context with only one family of module
instances. This avoids a clash between the instances indexed by `Fin 2` and those
indexed by `Fin (rankOneExtensionLowerShape t).length`.
