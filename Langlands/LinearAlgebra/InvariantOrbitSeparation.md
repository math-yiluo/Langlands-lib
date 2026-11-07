# Invariant functions separate orbits of characters

Worker 1800. Internal support for the proof of
`Langlands.GroupScheme.ClassFunctions.TorusSeparationStatement` (task
`0c854e73-f39c-45cf-9dda-31e34e1711f6`). In Steinberg's proof that class
functions separate semisimple conjugacy classes (R. Steinberg, *Regular
elements of semi-simple algebraic groups*, 1965, source
`steinberg-1965-regular-elements-semisimple-groups`, proof of Corollary 6.6,
printed p.63), one step is that the Weyl-invariant regular functions on a
maximal torus `T` separate the orbits of the Weyl group `W` on `T`; Steinberg
cites the general fact that invariants of a finite group separate its orbits.
This file proves that step for a torus described by its character lattice `M`:
a point of `T` with values in a field `k` is a homomorphism
`Multiplicative M →* k`, and a regular function on `T` is a finitely supported
`f : M →₀ k`. It then combines the step with the triangular spanning of
`Langlands.LinearAlgebra.DominantTriangularInvariants`. The Lean proof is an
original argument in any characteristic; it is not transcribed from a text.

## Setting

Namespace `Langlands.LinearAlgebra.DominantTriangular`. `M` is an additive
commutative group and `k` a field.

- `evalChar φ : (M →₀ k) →ₗ[k] k`, for `φ : Multiplicative M →* k`, sends `f`
  to `∑ μ, f μ * φ (ofAdd μ)`. It is defined as
  `Finsupp.linearCombination k (fun μ => φ (Multiplicative.ofAdd μ))`, and
  `evalChar_apply` gives the sum formula. This is the value at the point `φ` of
  the regular function `f`, written in the basis of characters.
- `IsInvariant W f` (from `DominantTriangularInvariants`) means
  `f (w μ) = f μ` for all `w ∈ W` and all `μ`.

Private helpers, used only in the proofs: evaluation at `φ` as a `k`-algebra map
on the group algebra `AddMonoidAlgebra k M` (`AddMonoidAlgebra.lift`), the
action of `w : M ≃ₗ[ℤ] M` on the group algebra (`AddMonoidAlgebra.domCongr`),
and the twisted homomorphism `μ ↦ φ (w μ)`.

## Results

- `exists_mem_eq_of_evalChar_eq`: let `W` be a finite subgroup of
  `M ≃ₗ[ℤ] M` and `φ ψ : Multiplicative M →* k`. If
  `evalChar φ f = evalChar ψ f` for every `W`-invariant `f`, then there is
  `w ∈ W` with `ψ (ofAdd μ) = φ (ofAdd (w μ))` for all `μ`.

  Proof. Suppose not. Then for each `w ∈ W` there is `μ_w` with
  `ψ (μ_w) ≠ φ (w μ_w)`. In the group algebra put
  `H = ∏_w (δ_{μ_w} - φ (w μ_w))`. Every translate `v · H` vanishes at `φ`,
  because its factor for `w = v` does. But `H` does not vanish at `ψ`, since
  no factor does. Let `Q = ∏_{v ∈ W} (X - v · H)`, a polynomial with
  coefficients in the group algebra. Left multiplication permutes `W`, so `Q`
  is fixed by `W` and its coefficients are `W`-invariant. By hypothesis `Q`
  has the same image under evaluation at `φ` as under evaluation at `ψ`. At
  `φ` the image is `X ^ |W|`. At `ψ` the image has the root `ψ(H)`, from its
  factor `v = 1`. Hence `ψ(H) ^ |W| = 0`, a contradiction. No power sums are
  used, so the argument works in every characteristic.

- `isInvariant_reflectionGroup_of_reflection`: for a root pairing `P` and a
  finitely supported `f : M →₀ R`, invariance under every root reflection
  `P.reflection i` implies invariance under `reflectionGroup P` (closure
  induction).

- `exists_mem_reflectionGroup_of_triangular` (`[Finite ι]`, base `b`): let
  `φ ψ : Multiplicative M →* k`. Suppose that every dominant `lam` admits a
  `reflectionGroup P`-invariant `c : M →₀ k` with `c lam = 1`,
  `lam - μ ∈ positiveCone P b` whenever `c μ ≠ 0`, and
  `evalChar φ c = evalChar ψ c`. Then `ψ (ofAdd μ) = φ (ofAdd (w μ))` for some
  `w ∈ reflectionGroup P`. Proof: the hypothesis puts these `c` in the kernel
  of `evalChar φ - evalChar ψ`. Triangular spanning
  (`isInvariant_mem_of_triangular`) then puts every invariant function in that
  kernel. The reflection group is finite (`finite_reflectionGroup`), so
  `exists_mem_eq_of_evalChar_eq` applies.

## Scope

This file is still pure algebra. It does not mention group schemes or
representations. In the application, `M` is the character lattice of a split
maximal torus and the functions `c` are the restrictions of trace characters of
highest-weight representations. Those inputs, and the step from `W`-conjugacy
to conjugacy in the group, are proved elsewhere.
