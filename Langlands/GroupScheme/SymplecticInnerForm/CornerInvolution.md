# Involutions of matrix algebras over division rings as adjoint involutions

Author: Worker 74, for Task 6243 (`d75aa284-b911-411c-8e33-34184b737113`). This module is
algebraic support for the proof of
`Langlands.GroupScheme.SymplecticInvolutionAntihermitianStatement` in
`SymplecticInnerForm/SymplecticInvolutionAntihermitian`. Declarations live in the namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`.

## Setting

`K` is a field, `D` a division ring with a `K`-algebra structure, `ι` a finite index type
with decidable equality, and `τ : FirstKindInvolution K (Matrix ι ι D)` an involution of the
first kind of `B = M_ι(D)`. No finiteness of `D` over `K`, no centrality and no simplicity
hypothesis is used. `single i j a` is the matrix unit `E_{ij}(a)`, and `θ.matrix ι` is the
published conjugate-transpose involution `y ↦ ᵗy^θ` with `(θ.matrix ι y) i j = θ (y j i)`.

## Main definitions and results

- `IsGramModel τ θ ε U U' : Prop`, for `θ : FirstKindInvolution K D`, `ε : K` and
  `U U' : Matrix ι ι D`, is the conjunction of `ε * ε = 1`, `U * U' = 1`, `U' * U = 1`,
  `θ.matrix ι U = ε • U` and `∀ y, τ y = U * θ.matrix ι y * U'`. It says that
  `τ = Int(U) ∘ θ*` with `ᵗU^θ = ε U`.
- `exists_isGramModel τ` (for nonempty `ι`): there exist `θ`, `ε`, `U`, `U'` with
  `IsGramModel τ θ ε U U'`. Moreover, if `ε = 1`, then for every `v ≠ 0` in `D` with
  `θ v = -v` there exist `θ'`, `U₂`, `U₂'` with `IsGramModel τ θ' (-1) U₂ U₂'`.

## The corner construction

Fix `i₀ : ι`, put `e = E_{i₀i₀}(1)` and `f = τ e`, an idempotent (`map_single_mul_map_single`).

- `IsCorner τ i₀ x` means `e * x = x` and `x * f = x`, so `x ∈ e B f`. The predicate is stable
  under `τ` (`IsCorner.map`). A corner element has zero rows outside `i₀`
  (`IsCorner.apply_eq_zero`), so a nonzero one has a nonzero entry `x i₀ q`
  (`IsCorner.exists_ne_zero`).
- `exists_isCorner_ne_zero`: since `f ≠ 0`, pick `f p q ≠ 0`. Then `E_{i₀p}(1) * f` is a
  nonzero corner element; its `(i₀, q)` entry is `f p q`.
- `exists_isCorner_eps`: for a nonzero corner element `x`, either `x + τ x ≠ 0`, which is a
  corner element with `τ`-eigenvalue `ε = 1`, or `τ x = -x`, giving `ε = -1`.
- `IsCorner.exists_quasiInverse`: for a nonzero corner element `x` with `x i₀ q ≠ 0`, the
  element `x' = f * E_{qi₀}((x i₀ q)⁻¹)` satisfies `x' * e = x'`, `x * x' = e` and
  `x' * x = f`. The second identity is an entry computation. For the third, `p = x' * x` is a
  nonzero idempotent in `f B f`. Then `τ p` is a nonzero idempotent in `e B e`, hence of the
  form `E_{i₀i₀}(a)` with `a * a = a`, `a ≠ 0` in the division ring `D`. So `a = 1`,
  `τ p = e` and `p = f`.
- `CornerData τ i₀` bundles `w`, `w'`, `ε` with `ε * ε = 1`, `e * w = w`, `w' * e = w'`,
  `w * w' = e`, `w' * w = f` and `τ w = ε • w`. `exists_cornerData` builds it from the
  previous two steps. Derived facts: `w * f = w`, `f * w' = w'`, `w ≠ 0` and
  `τ w' = ε • w'` (`map_w'`). The last holds because `w'' = ε • τ w'` satisfies `f w'' = w''`
  and `w w'' = e`, hence `w'' = w' w w'' = w'`.

## The involution of `D` and the Gram matrix

For `c : CornerData τ i₀`:

- `c.involution : FirstKindInvolution K D` is `θ a = (w * τ (E_{i₀i₀}(a)) * w') i₀ i₀`.
  `corner_eq` shows `w τ(E_{i₀i₀}(a)) w' = E_{i₀i₀}(θ a)`. Then `θ 1 = 1` holds because
  `w f w' = w w' = e`. Anti-multiplicativity follows from
  `τ(E(ab)) = τ(E b) f τ(E a)` and `f = w' w`. Involutivity comes from
  `w τ(w τ(E a) w') w' = ε² w w' E(a) w w' = E(a)`, using `τ w = ε w` and `τ w' = ε w'`.
- `map_single`: `τ (E_{i₀i₀}(a)) = w' * E_{i₀i₀}(θ a) * w`. This holds because
  `τ(E a) = f τ(E a) f = w' (w τ(E a) w') w`.
- `c.gram = U = ∑ k, τ (E_{i₀k}(1)) * w' * E_{i₀k}(1)` and
  `c.gramInv = U' = ∑ k, E_{ki₀}(1) * w * τ (E_{ki₀}(1))`.
- `map_single_eq_gram`: `τ (E_{ij}(a)) = U * ᵗ(E_{ij}(a))^θ * U'`. Indeed
  `U E_{ji}(θ a) U' = τ(E_{i₀j}) w' E_{i₀i₀}(θ a) w τ(E_{ii₀}) = τ(E_{i₀j}) τ(E_{i₀i₀}(a)) τ(E_{ii₀})`,
  and this equals `τ(E_{ii₀} E_{i₀i₀}(a) E_{i₀j})`. By linearity (`matrix_eq_sum_single`) this
  gives `map_eq_gram`: `τ y = U * ᵗy^θ * U'` for every `y`.
- `gram_mul_gramInv`: `U * U' = 1` is `map_eq_gram` at `y = 1`. `gramInv_mul_gram`:
  `U' * U = 1` follows by `mul_eq_one_symm`, since matrices over a division ring form a
  Dedekind-finite ring.
- `map_gram`: `τ U = ε • U` termwise, from `τ w' = ε • w'`. `matrix_gram`: then
  `ᵗU^θ = U' τ(U) U = ε • U`.
- `CornerData.isGramModel`: `IsGramModel τ c.involution c.ε c.gram c.gramInv`.

## Sign change

In `exists_isGramModel`, `i₀` is an arbitrary index. Given a corner datum `c` with `ε = 1`
and `v ≠ 0` with `θ v = -v` (`θ = c.involution`), the element `w₂ = E_{i₀i₀}(v) * w` is a
nonzero corner element. It satisfies
`τ w₂ = τ w * τ(E_{i₀i₀}(v)) = w τ(E(v)) = E(θ v) w = -w₂` (`w_mul_map_single`). A second
corner datum built from `w₂` has `ε = -1`.

## Provenance

Provenance: derived. The source is M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol,
*The Book of Involutions* (AMS Colloquium Publications 44, 1998; source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`). Theorem (4.2)(1), printed p.43
(PDF p.66), with proof on printed p.44 (PDF p.67), states that every involution of the first
kind of `End_E(M)` is adjoint to a hermitian or skew-hermitian form with respect to an
involution of the first kind of `E`. The present module proves this for `M_ι(D)` with `D` a
division ring.

The proof differs from KMRT. In the proof of (4.2), KMRT take an involution of `D` from
Theorem (3.1), extend it entrywise to `M_r(D)` and write the given involution as
`Int(g) ∘ *` with `g* = ±g` by Proposition (2.7), which rests on the Skolem–Noether theorem.
Here an explicit corner computation in `M_ι(D)` builds both the involution `θ` of `D` and the
Gram matrix `U` from `τ` itself. It uses neither Skolem–Noether nor centrality of `D`. In
(4.2) the involution of the coefficient algebra is fixed in advance. The sign change above,
which replaces `θ` by a new involution so that the form becomes skew-hermitian, is an
addition needed for the target statement.
