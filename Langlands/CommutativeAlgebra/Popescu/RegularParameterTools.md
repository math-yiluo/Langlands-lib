# Polynomial and tensor tools for adding regular parameters

Namespace `Langlands.CommutativeAlgebra.Popescu.RegularParameter`. Everything uses only the standard
axioms.

- `mem_span_monomial_of_X_mul` and `isWeaklyRegular_X`: the variables of `A[X₁, …, X_d]` form a
  weakly regular sequence, for any commutative ring `A`. Adapted from Worker 6's draft
  `ArtinianBottom`. Modulo `X_1, …, X_{i-1}`, an ideal spanned by monomials, multiplication by
  `X_i` is injective.
- `zVar`, `killZ`, `sub_rename_killZ_mem`: in `k[y₁, …, y_t, z₁, …, z_r] = MvPolynomial (Fin (t + r)) k`
  we have `y_i = X (castAdd i)` and `z_j = X (natAdd j)`. The retraction `killZ` sends `z ↦ 0` and
  satisfies `f − f(y, 0) ∈ (z)`, by induction on `f`.
- `comap_eq_map_sup_span` (P0): if `φ(z_j) ∈ q`, then `φ⁻¹(q) = (φ|_{k[y]})⁻¹(q)·k[y, z] + (z)`.
- `splitEquiv`: `k[y, z] ≃ (k[y])[z]` (`renameEquiv`, `sumAlgEquiv`), with `y_i ↦ C(y_i)` and
  `z_j ↦ X_j`.
- `extIdeal`: the extension `I k[y, z]` of an ideal `I ⊂ k[y]`.
- `isWeaklyRegular_quot` (P1): the `z_j` form a weakly regular sequence on `k[y, z]/I k[y, z]`. This
  ring is `≅ (k[y]/I)[z]` (`Ideal.quotientEquiv`, `quotientEquivQuotientMvPolynomial`).
- `isWeaklyRegular_transport`: weak regularity of a family on `R/J` transfers to `R/I` when `I = J`.
