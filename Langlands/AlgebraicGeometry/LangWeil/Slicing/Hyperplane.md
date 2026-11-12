# Hyperplane sections of an algebra with chosen generators

Author: Worker 5132.

This helper module defines the hyperplane sections used in the hyperplane-slicing step
`FamilyLangWeilSlicingStatement`, and records how they behave under base change.

Let `A` be an `R`-algebra with elements `g : Fin n → A` (in practice, generators that embed
`Spec A` into affine `n`-space over `R`). For an `R`-algebra `S` and coefficients
`α : Option (Fin n) → S`:

- `hyp R g α = α none ⊗ 1 + ∑ᵢ α (some i) ⊗ gᵢ ∈ S ⊗[R] A` is the equation of the affine
  hyperplane `α_* + ∑ᵢ αᵢ xᵢ = 0`, pulled back to `A`;
- `Slice R g α = (S ⊗[R] A) ⧸ (hyp R g α)` is the hyperplane section of `Spec A` over `S`.

With `S = R[a_*, a_0, …, a_{n-1}]` and `α` the variables, `Slice` is the universal hyperplane
section of the Library statement's Markdown. With `S` a field, it is a single hyperplane
section. The definitions are internal to this proof. They match the generic hyperplane `h` of
`BertiniGenericHyperplaneStatement` with the same indexing (`none` for the constant term).

## Declarations

- `map_hyp`, `rTensor_hyp`, `lift_hyp`: an algebra map `S → S'` sends `hyp R g α` to
  `hyp R g (f ∘ α)`. Under the homomorphism `S ⊗[R] A → κ` induced by a point
  `x : A →ₐ[R] κ`, the image is `α_* + ∑ᵢ αᵢ x(gᵢ)`. Proof: `simp`.
- `sliceBaseChange R g α : S' ⊗[S] Slice R g α ≃ₐ[S'] Slice R g (algebraMap S S' ∘ α)`: base
  change of the coefficient ring. Proof: Mathlib's `Algebra.tensorQuotientTensorEquiv` and
  `rTensor_hyp`.
- `sliceEquivOfEq`: equal coefficients give isomorphic sections.
- `slicePointsEquiv R g α`: the `S`-algebra maps `Slice R g α → κ` correspond to the points
  `x : A →ₐ[R] κ` with `α_* + ∑ᵢ αᵢ x(gᵢ) = 0`, that is, the points of `Spec A` on the
  hyperplane. Proof: `Algebra.TensorProduct.liftEquivRight` and the universal property of the
  quotient.
- `sliceCancelBaseChange R g k α`: for `R → k → S`, the hyperplane section of `k ⊗[R] A`
  (generators `1 ⊗ gᵢ`) with coefficients in `S` is the hyperplane section of `A`. Proof:
  `Algebra.TensorProduct.cancelBaseChange`, which sends the one hyperplane element to the other.
