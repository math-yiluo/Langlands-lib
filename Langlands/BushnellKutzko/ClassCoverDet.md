# Covering simple-character classes: determinant-invariant functionals are scalar

This module proves a linear-algebra lemma used for the fibre characters in
`ClassCoverFibreScalar`. It supplies the scalar step needed in the proof of Lemma (2.7) of
Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), printed
p. 121, when the given function `x ↦ ℓ(z(x - 1))` on `U^{k+1}` depends only on the determinant:
then `z` agrees with a scalar up to elements that `ℓ` pairs trivially with `𝔓^{k+1}`.

This is not a form of Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), (2.4.11), printed pp. 72–73. That lemma concerns a hereditary order `𝔄` in
`A = End_F(V)` with radical `𝔓` and the group `G = A^×`. Its coset clause gives the scalar: for
`n ∈ ℤ` and `b ∈ 𝔓^n`, if the coset `b + 𝔓^{1+n}` is intertwined by every element of `G`, then it
meets `F`. Its character clause goes the other way: for `m ≥ 0`, a character of `U^{m+1}(𝔄)`
intertwined by every element of the same group `G` factors through `det : G → F^×`. In the proof
of (2.7), BK94 apply the coset clause in the centralizer `B_γ` of `γ`, with the order
`𝔅_γ = 𝔄 ∩ B_γ` and the group `B_γ^×`: the quotient of the two extensions is `ψ_δ` on
`U^{m+1}(𝔅_γ)` for some `δ ∈ 𝔓^{-(m+1)} ∩ B_γ`; this character, hence the coset `δ + 𝔔^{-m}`
where `𝔔` is the radical of `𝔅_γ`, is intertwined by every element of `B_γ^×`, so the coset meets
the centre `F[γ]` of `B_γ` and `δ` may be taken in `F[γ]`. Here the
hypothesis is the determinant condition itself, and the proof is a direct computation with
elementary matrices.

## Elementary endomorphisms

Fix a basis `β` of a vector space `W` over a field `K`, and let `elementaryEnd β i j c` be the
Library's elementary endomorphism `E_{ij}(c)`, which sends `β_j` to `c β_i` and every other basis
vector to `0`.

* `elementaryEnd_mul_of_ne`: `E_{kl}(t) E_{l'j}(s) = 0` when `l ≠ l'`.
* `det_one_add_elementaryEnd_of_ne`: for `i ≠ j`, `1 + E_{ij}(c)` is a transvection and has
  determinant `1` (Mathlib's `Matrix.det_transvection_of_ne`).
* `det_one_add_elementaryEnd_self`: `1 + E_{ii}(c)` is diagonal, with determinant `1 + c`.

## The scalar lemma

`exists_scalar_of_det_invariant`. Let `K` be a nonarchimedean local field, `C` a lattice chain
in `W`, and `ℓ : End_K(W) → ℂ` a function with `ℓ 0 = 1`, `ℓ(a + b) = ℓ a · ℓ b` and
`ℓ(ab) = ℓ(ba)`. Let `z ∈ End_K(W)`, and suppose that, for `x, x'` in the unit filtration group
`U^{k+1}` of `C`, `det x = det x'` implies `ℓ(z(x - 1)) = ℓ(z(x' - 1))`. Then there is a scalar
`δ ∈ K` with `ℓ((z - δ) y) = 1` for every `y ∈ 𝔓^{k+1}`.

The proof takes a basis `β` splitting `C` (`LatticeChain.exists_basis_splits`), a fixed index
`i₀`, and `δ` the `(i₀,i₀)` entry of `z`. Write `y = Σ E_{ij}(y_{ij})`; each term lies in
`𝔓^{k+1}`, because the diagonal projections `E_{ii}(1)` lie in the order `𝔓^0`
(`LatticeChain.elementaryEnd_diag_mem_order`). Each `1 + E_{ij}(c)` with `E_{ij}(c) ∈ 𝔓^{k+1}`
lies in `U^{k+1}` (`LatticeChain.exists_mem_unitFiltration`). Comparing it with `1` for `i ≠ j`
gives `ℓ(z E_{ij}(c)) = 1`. For `i = j`, comparing `1 + E_{ii}(c)` with `1 + E_{i₀i₀}(c)`, which
lies in `U^{k+1}` by `LatticeChain.elementaryEnd_mem_iff`, gives
`ℓ(z E_{ii}(c)) = ℓ(z E_{i₀i₀}(c))`. The cyclic property and the multiplication rules of
elementary endomorphisms give the same identities for `z` replaced by `δ`, together with
`ℓ(z E_{i₀i₀}(c)) = ℓ(δ E_{i₀i₀}(c))`. Hence `ℓ((z - δ) E_{ij}(y_{ij})) = 1` for all `i, j`, and the
lemma follows by additivity.
