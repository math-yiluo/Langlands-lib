# Termination of the smoothening sequence: the Γ-trick

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. It supplies one of
the relations used in the defect count (the hypothesis `hQ1` of `exists_relation` in
`TerminationDilatation`). The argument is internal to this project.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: `C` is a commutative bialgebra over `R`, with counit `ε = counitAlgHom R C` and
cotangent module `Cot ε = I / I²`.

## Right translations

- `rtrans φ : C →ₐ[R] C` is right translation by an `R`-point `φ`, `c ↦ (id ⊗ φ)(Δ c)` followed by
  `C ⊗ R ≅ C` (`rtrans_apply`).
- `counit_rtrans`: `ε (rtrans φ c) = φ c`. `rtrans_counit`: `rtrans ε` is the identity. Both follow
  from the counit laws.

## Local ring `R`

- `evPt φ : k ⊗[R] C →ₐ[k] k` is evaluation at the reduction of an `R`-point `φ`
  (`evPt_tmul`: `evPt φ (a ⊗ c) = a · φ(c) mod 𝔪`).
- `entryMap l : C ⊗ C →ₗ[R] k ⊗ C` is `p ⊗ q ↦ l(dp) ⊗ q`, for a residue-field-valued form `l` on
  `Cot ε`.
- `l_dif_rtrans` (via `evPt_entryMap`): `l (d (rtrans φ c)) = evPt φ (entryMap l (Δ c))`. So the
  first-order part of a translate is the value at the point of a fixed element of `k ⊗ C`.

## Discrete valuation ring `R` with uniformizer `ϖ`

- `algebraMap_residue_eq_zero`: elements of `𝔪` map to `0` in `k`.
- `mem_maximalIdeal_of_det_ne_zero`: let `ψ` be a point with `ψ (z k) ∈ 𝔪` for all `k`, and let
  `ϖ b₀ + ∑ z_k b_k = 0`. Suppose the matrix `(l m (d (rtrans ψ (z k))))` has nonzero determinant.
  Then `ψ b₀` and all `ψ (b k)` lie in `𝔪`.

  Proof: apply `l m ∘ d ∘ rtrans ψ` to the relation. The Leibniz rule (`dif_mul`) and
  `counit_rtrans` give `∑_k ψ(b_k) H_{km} = 0` mod `𝔪`, so all `ψ(b_k) ∈ 𝔪`. Then
  `ϖ ψ(b₀) = -∑ ψ(z_k) ψ(b_k) ∈ (ϖ²)`, so `ψ(b₀) ∈ (ϖ)`.
- `gamma_trick` (**the Γ-trick**). Let `φ i` be a family of points with all `φ i (z k) ∈ 𝔪`. Let the
  forms `l m` be dual to the differentials of the `z k`: `l m (d z_k) = δ_{km}`. Suppose
  `ϖ b₀ + ∑ z_k b_k = 0`. Then there is `h ∈ C` with `ε h` a unit such that `φ i (h b₀) ∈ 𝔪` and
  `φ i (h b_k) ∈ 𝔪` for all `i, k`.

  Proof: let `H` be the matrix `(entryMap (l m) (Δ z_k))` over `k ⊗ C`. Choose `h` with
  `1 ⊗ h = det H` (`exists_one_tmul_eq`). The reduction of `ψ h` is the determinant of
  `(l m (d (rtrans ψ (z k))))` for every point `ψ`. At `ψ = ε` this matrix is the identity
  (`rtrans_counit`, duality), so `ε h` is a unit. At a point `φ i`, either the determinant vanishes
  and `φ i (h x) ∈ 𝔪` for every `x`, or `mem_maximalIdeal_of_det_ne_zero` applies.
