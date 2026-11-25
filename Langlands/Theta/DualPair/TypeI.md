# Type I dual pairs: the symplectic space `W ⊗ V`

**GKT §10.3.3** (the tensor product construction, p. 277) and **§10.5.2**, **Theorem 10.28**
(p. 288), for a field with involution: the book's Cases 1 (`D = E = F`, `τ = id`) and 3 (`D = E` a
quadratic extension of `F`, `τ` its conjugation).

The module `Langlands.Theta.DualPair.TypeI` builds the symplectic `F`-space of a Type I dual pair
from an `ε`-Hermitian and a `-ε`-Hermitian space, and the homomorphism of the product of their
isometry groups into its symplectic group.

## Setting and conventions

`K` is a field with an involution `τ` (a `RingInvo K`), `F` a field with `Algebra F K`, and
`hτ : ∀ a : F, τ(a) = a` (the fixed field of `τ` contains `F`). The spaces are left `K`-modules
with forms linear in the first variable, as in `Langlands.LinearAlgebra.EpsilonHermitian.Basic`:
`hW : EpsilonHermitianForm τ (-ε) W` and `hV : EpsilonHermitianForm τ ε V`; `W` is also an
`F`-module with `IsScalarTower F K W`, which makes `W ⊗[K] V` an `F`-module.

The book (Theorem 10.28) takes `W` a right space, `V` a left space and the form
`⟪w ⊗ v, w' ⊗ v'⟫ = tr_{D/F}(⟨w, w'⟩ · (v, v')^τ)` on `W ⊗_D V`. For a commutative `D = K` this is
the form below for the left space `^τW` (`d · w = w d^τ`, the same values `⟨w, w'⟩`, GKT
Proposition B.6) and the left space `V` with the action `d ⋆ v = d^τ v` and the form `(v, v')^τ`
(again `ε`-Hermitian and linear in the first variable): the relation `w d ⊗ v = w ⊗ d v` becomes
`(d^τ · w) ⊗ v = w ⊗ (d^τ ⋆ v)`, the `K`-balanced relation of `^τW ⊗_K V`. Equally, it is the
book's form for the right space `W` with `w d = d w` and the form `⟨w, w'⟩ = hW(w, w')^τ`, and the
left space `V` with `hV` itself: the relation is then that of `W ⊗_K V`, and
`tr(hW^τ · hV^τ) = tr(hW · hV)` because the trace is `τ`-invariant (`RingInvo.trace_conj`).

## Content

- `tensorPairing hW hV : W ⊗[K] V →ₛₗ[τ] (W ⊗[K] V →ₗ[K] K)`, with
  `tensorPairing (w' ⊗ v') (w ⊗ v) = hW(w, w') hV(v, v')` (`tensorPairing_tmul_tmul`), built with
  the semilinear `TensorProduct.lift`.
- `tensorHermitianForm hW hV : EpsilonHermitianForm τ (ε₁ * ε₂) (W ⊗[K] V)` for an `ε₁`-Hermitian
  `hW` and an `ε₂`-Hermitian `hV`: `⟨w ⊗ v, w' ⊗ v'⟩ = hW(w, w') hV(v, v')`
  (`tensorHermitianForm_tmul`). The symmetry `⟨y, x⟩ = ε₁ε₂ ⟨x, y⟩^τ` is checked on pure tensors
  (`tensorPairing_swap`).
- `tensorHermitianForm_nondegenerate`: for finite-dimensional `W`, `V` and non-degenerate `hW`,
  `hV`, the tensor form is non-degenerate. Proof: bases `bᵢ`, `dⱼ` with dual bases `cᵢ`, `eⱼ`
  (`EpsilonHermitianForm.exists_dual_basis`, from `exists_dual_family` of
  `Langlands.LinearAlgebra.EpsilonHermitian.Isotropic`); `x ↦ ⟨x, cₖ ⊗ eₗ⟩` is the coordinate of
  `x` at `bₖ ⊗ dₗ` in the basis `Basis.tensorProduct`.
- `tensorHermitianIsometry hW hV : U(W) × U(V) →* U(W ⊗ V)`, `(g, h) ↦ g ⊗ h` over `K`.
- `RingInvo.conjAlgEquiv hτ : K ≃ₐ[F] K` and `RingInvo.trace_conj`: `tr_{K/F}(a^τ) = tr_{K/F}(a)`.
- `tensorForm hτ hW hV : LinearMap.BilinForm F (W ⊗[K] V)`, `⟪x, y⟫ = tr_{K/F} ⟨x, y⟩`
  (`tensorForm_apply`), so `⟪w ⊗ v, w' ⊗ v'⟫ = tr_{K/F}(hW(w, w') hV(v, v'))` (`tensorForm_tmul`).
  It is `F`-linear in the second variable because `τ` fixes `F`.
- `tensorForm_swap`: `⟪y, x⟫ = -⟪x, y⟫` (the tensor form is skew-Hermitian, `(-ε) ε = -1`, and the
  trace is `τ`-invariant); `isAlt_tensorForm`: **alternating** for `2 ≠ 0` in `F`.
- `nondegenerate_tensorForm`: **non-degenerate** for `K / F` finite separable and `hW`, `hV`
  non-degenerate on finite-dimensional spaces: if `tr ⟨x, y⟩ = 0` for all `y`, then
  `tr(⟨x, y⟩ t) = tr ⟨x, t^τ y⟩ = 0` for all `t`; as the trace is not zero
  (`Algebra.trace_ne_zero`), `⟨x, y⟩ = 0`, and the tensor form is non-degenerate.
- `tensorIsometry hτ hW hV : U(W) × U(V) →* Sp(W ⊗ V)` (the isometry group
  `LinearMap.BilinForm.isometryGroup (tensorForm hτ hW hV)` of
  `Langlands.LinearAlgebra.Symplectic`),
  `(g, h) ↦ g ⊗ h` (`tensorIsometry_apply_tmul`); the embeddings `tensorIsometryLeft` (`g ↦ g ⊗ 1`)
  and `tensorIsometryRight` (`h ↦ 1 ⊗ h`), with `_apply_tmul` lemmas, whose images commute
  (`commute_tensorIsometryLeft_tensorIsometryRight`).

The mutual centralizer property (Proposition 10.22) is not proved here. The matrix form of Case
`3₊` (the Library's `U(ν, ν)` and `U(Q)` on `M_{α×2ν}(E)`) is identified with this construction in
`Langlands.Theta.DualPair.Unitary.TypeI`.

## Declarations

- `tensorPairing`, `tensorPairing_tmul_tmul`, `tensorPairing_swap`, `tensorHermitianForm`,
  `tensorHermitianForm_apply`, `tensorHermitianForm_tmul`, `EpsilonHermitianForm.exists_dual_basis`,
  `tensorHermitianForm_nondegenerate`, `tensorHermitianForm_congr`, `tensorHermitianIsometry`,
  `tensorHermitianIsometry_apply_tmul`.
- `tensorForm`, `tensorForm_apply`, `tensorForm_tmul`, `RingInvo.conjAlgEquiv`,
  `RingInvo.conjAlgEquiv_apply`, `RingInvo.trace_conj`, `tensorForm_swap`, `isAlt_tensorForm`,
  `nondegenerate_tensorForm`.
- `tensorIsometry`, `tensorIsometry_apply_tmul`, `tensorIsometryLeft`, `tensorIsometryRight`,
  `tensorIsometryLeft_apply_tmul`, `tensorIsometryRight_apply_tmul`,
  `commute_tensorIsometryLeft_tensorIsometryRight`.

In the name space `Langlands.Theta`, except `Langlands.EpsilonHermitianForm.exists_dual_basis` and
`Langlands.RingInvo.{conjAlgEquiv, conjAlgEquiv_apply, trace_conj}`.

## Dependencies

`Langlands.LinearAlgebra.EpsilonHermitian.Isotropic` (`exists_dual_family`),
`Langlands.LinearAlgebra.EpsilonHermitian.Determinant` (`RingInvo.conjRingHom`), Mathlib's
`TensorProduct.lift` (semilinear), `Basis.tensorProduct`, `Algebra.trace`,
`Algebra.trace_eq_of_algEquiv`, `Algebra.trace_ne_zero`.

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), §10.3.3,
p. 277; §10.5.2, Theorem 10.28, p. 288; Appendix B.2, Proposition B.6, p. 611.
