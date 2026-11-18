# Tits algebras of tensor products

This module carries out the tensor-product step of the additivity of the
Tits class (Tits, *Représentations linéaires irréductibles d'un groupe
réductif sur un corps quelconque*, J. reine angew. Math. 247 (1971),
Corollary 3.5, p. 205). Additivity compares the class of `λ + μ` with the
classes of `λ` and `μ`. The irreducible representation of highest weight
`λ + μ` occurs as a subquotient of the tensor product of the irreducible
representations of highest weights `λ` and `μ`. This module works with the ambient twisted-fixed algebra of the
tensor product: the Kronecker image of the two descended algebras. It proves
that this ambient twisted-fixed algebra is the tensor product of the
descended algebras, and that it contains the Tits algebra of the tensor
product. The subquotient step is separate.

Notation: `k ⊆ K` are fields, and `A ⊆ M_n(K)`, `B ⊆ M_m(K)` are
`k`-subalgebras. `⊗ₖ` is Mathlib's Kronecker product of matrices.

## Kronecker products of algebras

- `kroneckerLeft` (`X ↦ X ⊗ₖ 1`) and `kroneckerRight` (`Y ↦ 1 ⊗ₖ Y`) are
  `k`-algebra maps into `M_{n×m}(K)`. Their images commute, and
  `kroneckerLeft X * kroneckerRight Y = X ⊗ₖ Y`
  (`kroneckerLeft_mul_kroneckerRight`, via Mathlib's `mul_kronecker_mul`).
- `kroneckerTensor A B : A ⊗[k] B →ₐ[k] M_{n×m}(K)` is the induced algebra map
  (Mathlib's `Algebra.TensorProduct.lift`). It sends `X ⊗ Y` to `X ⊗ₖ Y`
  (`kroneckerTensor_tmul`).
- `kronecker_map_galois`: applying `σ` to the entries of `X ⊗ₖ Y` gives
  `σ(X) ⊗ₖ σ(Y)`.
- `range_kroneckerTensor_le_twistedFixed`: if `A ≤ twistedFixed P` and
  `B ≤ twistedFixed Q` (module `Algebra/GaloisTwistedMatrix`), then the image of
  `kroneckerTensor A B` lies in `twistedFixed (P ⊗ₖ Q)`. The twisted-fixed
  identities multiply under `mul_kronecker_mul`.
- `span_range_kroneckerTensor`: if `A` and `B` span the full matrix algebras over
  `K`, so does the image. Every `X ⊗ₖ Y` lies in the `K`-span of the image, by
  bilinearity and two span inductions, and matrix units are Kronecker
  products of matrix units (Mathlib's `single_kronecker_single`).
- `kroneckerTensor_injective`: let `K/k` be Galois, `n` and `m` nonempty, and `P σ`,
  `Q σ` invertible. Under the descent hypotheses, `A ⊗[k] B` is a simple ring
  (published `CentralSimple.isSimpleRing_tensor`, using `isCentral`,
  `isSimpleRing` and `finiteDimensional` of `GaloisTwistedMatrix`). So the
  nonzero ring map `kroneckerTensor A B` is injective (Mathlib's
  `IsSimpleRing.injective_ringHom_or_subsingleton_codomain`).
- `isUnit_kronecker`: the Kronecker product of invertible matrices is
  invertible (`det_kronecker`).
- `kroneckerCSA` (for `K/k` Galois, `n` and `m` nonempty, `P σ` and `Q σ`
  invertible, `A ≤ twistedFixed P`, `B ≤ twistedFixed Q` and both spanning) is
  the image as a central simple algebra, via `toCSA` for `P ⊗ₖ Q`. Under the
  same hypotheses, `kroneckerCSA_isBrauerEquivalent` shows that it is Brauer
  equivalent to the published `Langlands.Brauer.tensor` of the two descended
  algebras, since `AlgEquiv.ofInjective` identifies it with `A ⊗[k] B`. The
  nonemptiness of `n` and `m` is necessary: for an empty index the image is
  the zero algebra, which is not simple.

## Tensor products of representations

Let `G` be affine over `k`, and let `ρ`, `τ` be representations of `G_K` on
`Kⁿ` and `Kᵐ`. The published `MatrixRepresentation.tensor` is their tensor
product.

- `universalMatrix_tensor`: the universal matrix of `ρ.tensor τ` is the
  Kronecker product of the universal matrices. This is the published
  `tensor_affineMatrix_entry` at the universal scalar point.
- `titsAlgebra_tensor_le`: the Tits algebra of `ρ.tensor τ` lies in the image of
  `kroneckerTensor (titsAlgebra ρ) (titsAlgebra τ)`. By `exists_reconstruction`,
  the entries of both universal matrices are `Σ_s (id ⊗ ψ_s)(z) (1 ⊗ o_s)`. Hence
  every coefficient matrix of the tensor product is
  `Σ_{s,t} φ(o_s o_t) · X_{ψ_s}(ρ) ⊗ₖ X_{ψ_t}(τ)`, with coefficients
  `φ(o_s o_t) ∈ k`.

There is no restriction on the characteristic and no perfectness or
reducedness assumption. `K/k` may be an infinite Galois extension.
