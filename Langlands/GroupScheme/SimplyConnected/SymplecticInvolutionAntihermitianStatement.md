# Symplectic involutions are adjoint to antihermitian division forms: statement

Author: Worker 74, for Task 6243 (`d75aa284-b911-411c-8e33-34184b737113`), coordinated with
Worker 246. The module contains one `Prop`-valued definition and no proof.

## Statement

`Langlands.GroupScheme.SymplecticInvolutionAntihermitianStatement.{u}` quantifies over

- a field `K : Type u` and a `K`-algebra `A : Type u` that is central (`Algebra.IsCentral`),
  simple (`IsSimpleRing`) and finite-dimensional;
- an involution of the first kind `τ : Quaternionic.FirstKindInvolution K A` (a `K`-linear
  anti-automorphism of order two, module `Quaternionic/Involution`);
- a natural number `n`, a field `L : Type u` with a `K`-algebra structure, and an `L`-algebra
  isomorphism `e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L`.

The hypothesis is that `e` carries the scalar extension `τ.baseChange L` (the map
`id_L ⊗ τ`) to the adjoint involution of the standard alternating matrix
`J = Matrix.J (Fin n) L`, written without inverses as

`e (τ_L x) * J = J * (e x)ᵀ` for every `x : L ⊗[K] A`.

Since `J * J = -1`, this says `e (τ_L x) = J (e x)ᵀ J⁻¹`. The equation holds over the given
field `L`; no Galois or finiteness condition on `L/K` is required.

The conclusion asserts that there are

- natural numbers `degree` and `m`, with `NeZero m`, `0 < degree` and `m * degree = 2 * n`;
- a division ring `D : Type u` that is a central finite-dimensional `K`-algebra with
  `Module.finrank K D = degree ^ 2`;
- an involution of the first kind `σ` of `D` whose symmetric space
  `σ.symmetricSubspace = {x | σ x = x}` has `K`-dimension `degree * (degree + 1) / 2`;
- a Gram matrix `H : Matrix (Fin m) (Fin m) D` with `σ.IsAntihermitian H` and `IsUnit H`;
- a `K`-algebra isomorphism `φ : A ≃ₐ[K] Matrix (Fin m) (Fin m) D` such that
  `φ (τ x) * H = H * σ.matrix (Fin m) (φ x)` for every `x : A`.

Here `σ.matrix (Fin m) y` is the conjugate transpose `ᵗy^σ`, with entries
`(σ.matrix y) i j = σ (y j i)`. `σ.IsAntihermitian H` (module `Quaternionic/Forms`) means
`ᵗH^σ = -H` and every diagonal entry `H i i` lies in `{a - σ a}`; the second condition is the
trace-valued (alternating) condition, which matters in characteristic two. Since `H` is a
unit, the last equation says that `φ` carries `τ` to the adjoint involution
`y ↦ H ᵗy^σ H⁻¹` of the form with Gram matrix `H`. The equation is stated by multiplying
through by `H`, since `Matrix (Fin m) (Fin m) D` over a noncommutative `D` carries no
`Inv` instance.

The existential block from `degree` to `IsUnit H` repeats, field by field, the algebra,
involution and form data of the published target
`Langlands.GroupScheme.SymplecticInnerFormAntihermitianStatement`. The final clause supplies
the algebra isomorphism that identifies the group of `(A, τ)` with `σ.symplecticGroup H`.

## Role

This is the purely algebraic step in the planned proof of
`SymplecticInnerFormAntihermitianStatement` (Task 6243). It is meant to consume the output of
`Langlands.GroupScheme.SymplecticInnerFormInvolutionStatement` (Worker 246): a central
simple algebra `A` of degree `2n` with an involution `τ` and a finite Galois chart `e`
satisfying exactly the displayed equation (the predicate
`SymplecticInnerForm.HasStandardSymplecticSplitting τ n`). The comparison of the group of
`(A, τ)` with `σ.symplecticGroup H` is a separate step.

## Source and provenance

Provenance: derived.

M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS
Colloquium Publications 44, 1998, source `knus-merkurjev-rost-tignol-1998-book-of-involutions`:

- §4, Theorem (4.2)(1), printed p.43 (PDF p.66), with proof on printed p.44 (PDF p.67): for
  `A = End_E(M)` and an involution `θ` of the first kind on `E`, every involution of the first
  kind on `A` is the adjoint involution `σ_h` of a nonsingular hermitian or skew-hermitian
  form `h`. If `char F ≠ 2`, `σ_h` and `θ` have opposite types when `h` is skew-hermitian; if
  `char F = 2`, `σ_h` is symplectic if and only if `h` is alternating. The proof reduces to
  `A = M_r(D)` with `D` a central division algebra carrying an involution of the first kind
  (Theorem (3.1)).
- §2, Definition (2.5) and Proposition (2.6), printed pp.16–17 (PDF pp.39–40): an involution of
  the first kind is symplectic when, over a splitting field, it is adjoint to an alternating
  form. For an involution of the first kind on a central simple algebra of degree `d`, if
  `char F ≠ 2` the symmetric space has dimension `d(d + 1)/2` for orthogonal and `d(d - 1)/2`
  for symplectic type; if `char F = 2` it has dimension `d(d + 1)/2` in both cases, and the
  involution is symplectic if and only if `1 ∈ Alt(A, σ) = {a - σ a}`.

The Lean statement is derived from these sources as follows. "`τ` is symplectic" is expressed
by an actual splitting chart to the adjoint involution of `J`, as in Definition (2.5). The
conclusion is Theorem (4.2)(1) specialized to a symplectic involution and with `E = D` a
division algebra, so that `M = D^m` and `A ≅ M_m(D)`. The involution `σ` of `D` is chosen with
`H` skew-hermitian. When `char K ≠ 2`, Theorem (4.2)(1) then makes `σ` orthogonal, which by
Proposition (2.6) is the stated dimension of the symmetric space. When `char K = 2` that
dimension holds for every involution of the first kind, and the alternating condition on `h`
is the trace-valued clause of `σ.IsAntihermitian H`. The Lean conclusion fixes the conventions
`ᵗH^σ = -H` and `φ (τ x) * H = H * ᵗ(φ x)^σ`, and it adds the numerical consequences
`m * degree = 2 * n` and `finrank K D = degree ^ 2`.
