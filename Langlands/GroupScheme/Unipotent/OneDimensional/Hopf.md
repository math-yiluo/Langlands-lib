# Rigidity, cocommutativity and exponent of one-dimensional unipotent coordinate rings

Worker 716. Internal lemmas for the proof of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement`. They
concern a corepresented group: a functor `F` from commutative `k`-algebras to
groups whose underlying set functor is corepresented by a commutative
`k`-algebra `B`, via `e`. `B` carries the Library bialgebra structure
`AffineLinearEmbedding.bialgebra e` with comultiplication `comul e` and counit
`counit e`. No registered source was used. The proofs are the implemented ones.

## Rigidity in a domain

- `eq_algebraMap_of_isIntegral`: in a domain `A` with a `k`-point `χ`, every
  element integral over `k` equals the constant `χ(a)`. Otherwise `a - χ(a)`
  is a nonzero algebraic element killed by `χ`. The Library lemma
  `transcendental_of_augmentation_eq_zero` says such an element is
  transcendental, a contradiction.
- `eq_comp_of_finite`: let `f : C → A` be an algebra map into such a domain
  that kills an element `y` with `C/(y)` finite-dimensional. Then `f` is the
  constant map `ofId ∘ χ ∘ f`. Indeed, `f` factors through the finite
  algebra `C/(y)`, so its values are integral over `k`.

## An injectivity lemma

`tensorEval φ y : R[X] → S ⊗ T` sends `∑ rᵢ Xⁱ` to `∑ φ(rᵢ) ⊗ yⁱ`.
`tensorEval_eq_map` factors it as `(φ ⊗ aeval y) ∘ polyEquivTensor`.
`tensorEval_injective` shows it is injective when `φ` is injective and `y` is
transcendental, because tensor products of injective maps over a field are
injective (`TensorProduct.map_injective_of_flat_flat`).

## Points

`val e x : B →ₐ[k] A` is the algebra map classifying a point `x ∈ F(A)`. It is
injective in `x` (`val_injective`) and inverse to `pt e` (`val_pt`). The Library
coordinate API gives `val_mul` (product of points = `productMap` after
`comul e`), `val_one` (the counit) and `val_map` (naturality). `univ e` is the
universal point, classified by the identity of `B`.

- `map_eq_one`: let `χ` be a `k`-point of `A`. If the composite of `val e x`
  with `χ` is the counit, then `x` becomes `1` in `F(k)`.
- `eq_one_of_val_eq_zero` (**rigidity**): let `A` be a domain with a
  `k`-point `χ` and let `x ∈ F(A)` become trivial at `χ`. If `x` kills some
  `y ∈ B` (`val e x y = 0`) with `B/(y)` finite-dimensional, then `x = 1`.
  This applies `eq_comp_of_finite` to `val e x`.
- For a primitive `y`, `val_mul_apply`, `primHom`, `val_inv_apply` and
  `val_pow_apply` show that `x ↦ val e x y` is a homomorphism to the additive
  group.

## Cocommutativity and exponent

`comm_comp_comul`: suppose `B ⊗ B` is a domain and some primitive `y` has
`B/(y)` finite-dimensional. Then `comul e` is cocommutative. Take `x₁, x₂` to be
the points of `F(B ⊗ B)` given by the two inclusions and `χ = ε ⊗ ε`. The
commutator `x₁ x₂ x₁⁻¹ x₂⁻¹` kills `y` because `y` is primitive. It is trivial
at `χ` because each `xᵢ` is (`map_eq_one`). Rigidity gives `x₁ x₂ = x₂ x₁`.
Applying `val` turns this identity into `comm ∘ comul = comul`.

`univ_pow_char`: in characteristic `p`, if `B` is a domain and some primitive
`y` has `B/(y)` finite-dimensional, then `(univ e)^p = 1`. The point
`(univ e)^p` sends `y` to `p y = 0` and is trivial at the counit, so rigidity
applies with `A = B`. `val_univ_pow_succ` records the convolution recursion
for the powers of the universal point.
