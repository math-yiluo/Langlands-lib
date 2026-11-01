# The ultrametric projective tensor seminorm

This module defines the tensor-product seminorm of Ben Yaacov,
*Tensor products of valued fields* (Bull. London Math. Soc. 47 (2015)),
source `ben-yaacov-2015-tensor-products-valued-fields`, Definition 6, printed
page 2:

`‖z‖ = inf_{z = x̄ᵗ ⊗ ȳ} max_i ‖x_i‖ ‖y_i‖`.

The module proves the parts of Lemma 7 (same page) needed downstream: the
seminorm is a sub-multiplicative ring seminorm, it satisfies the strong
triangle inequality, it is at most `‖a‖ ‖b‖` on a pure tensor `a ⊗ₜ b`, and
it equals `1` at `1`.

## Setting and the definition

Let `E` be a commutative ring, and let `F` and `G` be normed rings that are
`E`-algebras. No compatibility between the norms and `E` is needed for the
definition.

- `UltrametricTensorSeminorm.Representation E F G t` is a finite
  representation of `t : F ⊗[E] G`. It consists of a finite index type
  `ι : Type`, left factors `left : ι → F`, right factors `right : ι → G`, and a
  proof that `∑ i, left i ⊗ₜ right i = t`. Every finite sum can be indexed by
  some `Fin n`, so the restriction `ι : Type` loses nothing.
- `Representation.value r` is `max_i ‖left i‖₊ * ‖right i‖₊` in `ℝ≥0`
  (`Finset.sup`, which is `0` for the empty representation).
- `UltrametricTensorSeminorm.seminormFun t : ℝ≥0` is the infimum of
  `r.value` over all representations `r` of `t`. Every tensor has a
  representation (`Representation.nonempty`, by induction on tensors), so this
  is an infimum over a nonempty set bounded below by `0`.
- `ultrametricTensorSeminorm E F G : RingSeminorm (F ⊗[E] G)` is
  `seminormFun`, coerced to `ℝ`. `ultrametricTensorSeminorm_apply` records
  this.

This is formula (1) of Definition 6 for the algebraic tensor product. The
source states it for standard semi-normed vector spaces over a standard valued
field. Here it is stated for normed rings over a commutative ring.

## Seminorm laws (Lemma 7(i))

Representations combine as follows:

- `Representation.zero` is the empty representation of `0`, with value `0`;
- `Representation.tmul a b` is the one-term representation of `a ⊗ₜ b`, with
  value `‖a‖₊ * ‖b‖₊` (`value_tmul`);
- `Representation.add` concatenates two representations (index type `ι ⊕ ι'`).
  The value of the result is at most the larger of the two values
  (`value_add_le`);
- `Representation.neg` negates the left factors and keeps the value
  (`value_neg`);
- `Representation.mul` takes termwise products
  `(left i * left' j) ⊗ₜ (right i * right' j)` over `ι × ι'`. It represents
  the product by `Algebra.TensorProduct.tmul_mul_tmul`. Its value is at most
  the product of the two values (`value_mul_le`), using `‖x y‖ ≤ ‖x‖ ‖y‖` in
  `F` and in `G`.

Taking infima gives `seminormFun_zero`, `seminormFun_tmul_le`,
`seminormFun_add_le` (strong triangle inequality, via
`exists_lt_of_ciInf_lt`), `seminormFun_neg` and `seminormFun_mul_le` (via
`NNReal.le_iInf_mul` and `NNReal.le_mul_iInf`). These give the
`RingSeminorm` structure and the theorems:

- `isNonarchimedean_ultrametricTensorSeminorm`:
  `p (s + t) ≤ max (p s) (p t)`;
- `ultrametricTensorSeminorm_tmul_le`: `p (a ⊗ₜ b) ≤ ‖a‖ * ‖b‖`.

The strong triangle inequality comes from the `max` in the definition. It
holds even when the norms of `F` and `G` are not ultrametric. Only the upper
bound half of Lemma 7(iii) is proved for general pure tensors.

## Normalization at one

The lower bound is proved under these hypotheses: `E`, `F` and `G` are normed
fields, `F` and `G` are normed `E`-algebras, and the norms of `F` and `G` are
ultrametric (`IsUltrametricDist`). Then `algebraMap E F` and `algebraMap E G`
preserve norms (`norm_algebraMap'`), and `‖c • x‖ = ‖c‖ ‖x‖`. No field needs
to be complete, and `E` is not assumed ultrametric.

- `one_le_of_linearIndependent`: suppose `∑ i, a i ⊗ₜ b i = 1` with the right
  factors `b` linearly independent over `E`, and `‖a i‖ * ‖b i‖ ≤ M` for all
  `i`. Then `1 ≤ M`. A left inverse `g` of the injective map
  `Fintype.linearCombination E b` gives coordinate functionals with
  `g (b i) = Pi.single i 1`. Applying `id ⊗ (j-th coordinate of g)` and
  `TensorProduct.rid` to the identity shows that `a j = algebraMap E F (g 1 j)`.
  A linear left inverse `ψ` of `algebraMap E F` then turns the identity, via
  `ψ ⊗ id` and `TensorProduct.lid`, into `∑ i, g 1 i • b i = 1` in `G`. The
  ultrametric inequality in `G`
  (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`) and
  `‖g 1 i • b i‖ = ‖a i‖ ‖b i‖` give `1 = ‖1‖ ≤ M`. The empty index type is
  impossible because `1 ≠ 0` in `G`.
- `one_le_aux`, proved by strong induction on the number of terms, removes
  linear dependence among the right factors. This is the reduction in the
  proof of Lemma 7(ii), applied to the right factors instead of the left
  ones. If the `b i` are dependent, `∑ i, c i • b i = 0` with some
  `c j ≠ 0`. If `b j = 0`, take `k = j` and `d = 0`. Otherwise choose `k`
  maximizing `‖c i‖ * ‖b i‖`; then `c k ≠ 0`, because
  `‖c k‖ * ‖b k‖ ≥ ‖c j‖ * ‖b j‖ > 0`, and `d i = -(c k)⁻¹ * c i`. In both
  cases `b k = ∑_{i ≠ k} d i • b i` and `‖d i‖ * ‖b i‖ ≤ ‖b k‖`. The
  representation
  `∑_{i ≠ k} (a i + d i • a k) ⊗ₜ b i` of `1` has one term fewer. By the
  ultrametric inequality in `F`, each new term satisfies
  `‖a i + d i • a k‖ * ‖b i‖ ≤ max (‖a i‖ ‖b i‖, ‖a k‖ ‖b k‖) ≤ M`.
- `one_le_of_sum_tmul_eq_one` and `one_le_value`: every representation of
  `1` has value at least `1`.
- `ultrametricTensorSeminorm_one`: `p 1 = 1`. The upper bound comes from
  `1 = 1 ⊗ₜ 1` and `seminormFun_tmul_le`.

The source proves Lemma 7(iii) from Lemma 7(ii). The Lean proof proves only
the case `x = y = 1`, by the same reduction and a direct dual-functional
argument for independent right factors.

## Exported existence result

`exists_ultrametricTensorSeminorm` takes normed fields `E`, `F`, `G` with
ultrametric `F` and `G` and normed `E`-algebra structures. It gives
`∃ p : RingSeminorm (F ⊗[E] G), p 1 = 1 ∧ IsNonarchimedean p ∧ (∀ a, p (a ⊗ₜ 1) ≤ ‖a‖) ∧ (∀ b, p (1 ⊗ₜ b) ≤ ‖b‖)`,
with witness `ultrametricTensorSeminorm E F G`. The bound on `a ⊗ₜ 1` comes
from `ultrametricTensorSeminorm_tmul_le` and `‖1‖ = 1`, and the same holds for
`1 ⊗ₜ b`. This is the body of
`Langlands.Analytic.TensorSeminormStatement`, with no completeness hypotheses
and no ultrametric hypothesis on `E`. That proposition follows by
instantiating this theorem; this module does not import it.

## Provenance

Source: Definition 6 and Lemma 7(i)–(iii) of Ben Yaacov 2015, printed
page 2. Definition 6 cites [BGR84, 2.1.7] (Bosch–Güntzer–Remmert). The
generalization of the setting to normed rings over a commutative ring, and the
right-factor version of the Lemma 7(ii) reduction combined with the
dual-functional argument, are internal adaptations made for the Lean proof.
