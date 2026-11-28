# Unit eigenvectors of a cyclic automorphism over a ring with trivial Picard group

The module `Langlands.CommutativeAlgebra.KummerEigenvector` proves the
algebraic core of Kummer theory over a base ring `A` that need not be a field.
Let `ℓ` be a positive integer and `σ` an algebra endomorphism with `σ^ℓ = 1`
whose fixed points are the image of `A`. Suppose `B` is a faithful
`A`-algebra, `A` has trivial Picard group, and over every maximal ideal of `A`
there is a field point `φ` of `B` with `φ ∘ σ^j ≠ φ` for `0 < j < ℓ`. Then
for each `c ∈ A` with `c^ℓ = 1`, `σ` has a unit eigenvector with
eigenvalue `c`. The commutative rings `A` and `B` lie in one universe `u`,
and `σ : B →ₐ[A] B`. The declarations are in
`Langlands.CommutativeAlgebra.KummerEigenvector`.

## Eigenspaces and resolvents

- `eigenspace σ d` is the `A`-submodule `{b | d · σ(b) = b}` of `B`
  (`mem_eigenspace_iff`). Thus `b ∈ eigenspace σ d` means `σ(b) = d⁻¹ b`
  when `d` is a unit.
- `eigenspace_mul_le`: `E(d) · E(d') ≤ E(d d')` as submodule products.
- `eigenspace_one_le`: if the fixed points of `σ` are exactly the image of
  `A`, then `E(1) ≤ 1`, the submodule spanned by `1`.
- `resolvent σ ℓ d b` is the Lagrange resolvent `∑_{j<ℓ} d^j σ^j(b)`.
- `resolvent_mem`: if `σ^ℓ = 1` and `d^ℓ = 1`, the resolvent lies in `E(d)`
  (reindex the sum after applying `σ`).
- `exists_resolvent_ne_zero` (Dedekind independence): if `0 < ℓ`, `φ : B →+* K`
  is a ring map to a field and the maps `φ ∘ σ^j`, `j < ℓ`, are pairwise
  distinct, then for each `d` some resolvent has nonzero image under `φ`.
  (For `ℓ = 0` every resolvent is the empty sum `0`.) Otherwise
  `∑_j φ(d)^j (φ ∘ σ^j) = 0` as functions on `B`, contradicting Mathlib's
  linear independence of distinct monoid homomorphisms
  (`linearIndependent_monoidHom`) at the coefficient `φ(d)^0 = 1`.

## The main theorem

`exists_unit_eigenvector` assumes `[FaithfulSMul A B]`,
`[Subsingleton (CommRing.Pic A)]`, `0 < ℓ`, `σ^ℓ = 1`, that every fixed point
of `σ` is the image of an element of `A`, and that for every maximal ideal `𝔪`
of `A` there are a field `K : Type u` and a ring map `φ : B →+* K` killing the
image of `𝔪` with `φ ∘ σ^j ≠ φ` for `0 < j < ℓ`. For `c ∈ A` with `c^ℓ = 1`
it gives a unit `v` of `B` with `σ(v) = c · v` and a unit `w` of `A` with
`v^ℓ = w` in `B`.

Proof as implemented:

1. Put `e = c^(ℓ-1)`, so `c e = 1` and `e^ℓ = 1`. The hypothesis on the maps
   `φ` gives pairwise distinctness of `φ ∘ σ^i`, `i < ℓ` (if
   `φ σ^i = φ σ^j` with `i < j`, compose with `σ^(ℓ-i)` to get
   `φ = φ σ^(j-i)`).
2. Let `E₁ = E(e)` and `E₂ = E(c)`. Then `E₁ E₂ ≤ E(1) ≤ 1`. If `1 ∉ E₁ E₂`,
   the ideal `J` of `a ∈ A` with `a ∈ E₁ E₂` is proper, hence contained in a
   maximal ideal `𝔪`. For the map `φ` over `𝔪`, choose resolvents
   `r₁ ∈ E₁`, `r₂ ∈ E₂` with `φ(r₁), φ(r₂) ≠ 0`. Their product lies in
   `E₁ E₂ ≤ 1`, so it equals some `a ∈ J ⊆ 𝔪`, and `φ` kills it, a
   contradiction. Hence `E₁ E₂ = 1`.
3. So `E₁` is a unit of the monoid of `A`-submodules of `B`, with inverse `E₂`.
   Its class in `CommRing.Pic A` is trivial, and Mathlib's exact sequence
   `Submodule.ker_unitsToPic` (for a faithful algebra) gives a unit `v` of `B`
   whose span is `E₁`. Then `e σ(v) = v`, so `σ(v) = c v`.
4. `σ(v^ℓ) = c^ℓ v^ℓ = v^ℓ` and likewise `σ(v^(-ℓ)) = v^(-ℓ)`, so both are
   images of elements of `A`; their product is `1`, and faithfulness of the
   algebra gives a unit `w` of `A` with `v^ℓ = w`.

## Provenance

For a cyclic degree-`ℓ` extension of fields, Hilbert's Theorem 90 supplies
an eigenvector of a Galois generator for each base-field scalar `c` with
`c^ℓ = 1`. Here the pointwise freeness hypothesis and Dedekind's
independence of characters give an invertible eigenspace, and triviality of
`Pic A` gives a unit generator via `Submodule.ker_unitsToPic`. The
application takes `A = R[1/t]` for a regular local ring `R`, using
`regularLocalAwayPicard` to show that `Pic A` is trivial.
