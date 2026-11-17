# Rigidity of bialgebra maps to group algebras modulo an ideal

This module is an internal helper for the proof of
`Langlands.GroupScheme.MultiplicativeTypeCompleteLocalDeformationStatement`. Its route is
our own; it replaces the deformation-theoretic uniqueness argument in Conrad's notes
(Appendix B, B.3.2) by a direct computation with convolution idempotents.

## Setting

`K` is a commutative ring, `A` a `K`-coalgebra (later a commutative bialgebra), and `N` an
additive commutative group. For a bialgebra map `π : A → K[N]` and `n : N`, the linear form
`coeffForm π n : A → K` is `a ↦ (π a).coeff n` (from the published module
`Langlands.Algebra.GroupAlgebraCoaction`, which also supplies the convolution `conv` and the
right action `ract`).

## Convolution lemmas

- `conv_eq_comp_ract`: `conv f g = f ∘ ract g`.
- `conv_assoc`, `conv_add_left`, `conv_add_right`, `conv_sub_left`, `conv_sub_right`,
  `conv_smul_right`: convolution of linear forms `A → K` is associative and bilinear.
- `ValuesIn J f` (a definition) says that the linear form `f` takes all its values in the
  ideal `J`. Lemmas `ValuesIn.add`, `.sub`, `.smul`, `.mono` are closure properties;
  `ValuesIn.conv_mul` gives `ValuesIn (J * J') (conv f g)` from `ValuesIn J f` and
  `ValuesIn J' g`; `ValuesIn.conv_left` and `ValuesIn.conv_right` give `ValuesIn J` of a
  convolution when one factor has values in `J`.
- The private definition `evalPair f g` is the linear form `a ⊗ b ↦ f a * g b` on `A ⊗ A`;
  the private lemmas `evalPair_comm` (swapping the factors through `TensorProduct.comm`) and
  `evalPair_mem` (the value lies in `J` when `f` has values in `J`) are used only inside
  this module.
- `ValuesIn.conv_sub_conv_comm`: if `comul a - comm (comul a) ∈ I • ⊤` for all `a` (the
  coalgebra is cocommutative modulo `I`) and `f` has values in `J`, then
  `conv f g - conv g f` has values in `I * J`.

## Main results

- `coeff_sub_mem_pow I hcomm π π' h`: if `A` is a bialgebra cocommutative modulo `I`, and
  `π π' : A →ₐc[K] K[N]` are bialgebra maps with `(π a).coeff n - (π' a).coeff n ∈ I` for all
  `a` and `n`, then for every `k` the same difference lies in `I ^ (k + 1)`.
- `eq_of_coeff_sub_mem I hsep hcomm π π' h`: if moreover `K` is `I`-adically separated
  (every `x` lying in all `I ^ k` is zero), then `π = π'`.

## Proof

Fix `n` and put `f = coeffForm π n`, `g = coeffForm π' n`. Because `π` and `π'` are
bialgebra maps, `f` and `g` are convolution idempotents (`conv_coeffForm`). Induct on `k`,
assuming `d = f - g` has values in `I ^ (k + 1)` and writing `J' = I ^ (k + 2)`.

1. Expanding `conv f f - conv g g` gives `d = conv d f + conv g d`.
2. `conv d f - conv d g = conv d d` has values in `I ^ (2k + 2) ⊆ J'`.
3. `conv d g - conv g d` has values in `I * I ^ (k + 1) = J'` by cocommutativity modulo `I`.
4. Hence `d - 2 e` has values in `J'`, where `e = conv g d`.
5. Convolving with `g` on the left and using `conv g g = g` turns `d - 2e` into `-e`, so `e`
   has values in `J'`; therefore so does `d`.

Separatedness then forces every difference of coefficients to vanish, and bialgebra maps to
`K[N]` are determined by their coefficients.
