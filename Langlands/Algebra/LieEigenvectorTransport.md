# Transport of eigenvectors of inner derivations

The module `Langlands.Algebra.LieEigenvectorTransport` collects three elementary facts used to
move statements about eigenvectors of an inner derivation `ad h` between Lie algebras.

## Main results

- `lie_eq_smul_iff`, `eigenSet_eq_image`, `span_eigenSet_eq_map`: an isomorphism of Lie algebras
  `e : L₁ ≃ₗ⁅R⁆ L₂` satisfies `⁅e h, e X⁆ = c • e X ↔ ⁅h, X⁆ = c • X`; consequently, for any family
  of eigenvalues `μ i`, the eigenvectors of `e h` are the images of the eigenvectors of `h`, and
  the span of the former is the image under `e` of the span of the latter.
- `one_tmul_lie`: on a scalar extension `A ⊗[R] L`, the inner derivation of `1 ⊗ h` is the scalar
  extension of the inner derivation `LieAlgebra.ad R L h` (checked on pure tensors with
  `LieAlgebra.ExtendScalars.bracket_tmul`).
- `mem_span_restrictScalars_iff`, `span_restrictScalars_eq_top`: let `F / k` be a field extension
  and `S` a set of vectors of an `F`-vector space `M` that is stable under multiplication by
  scalars of `F`. Then a vector lies in the `k`-span of `S` inside `RestrictScalars k F M` exactly
  when it lies in the `F`-span of `S`; in particular `S` spans over `k` if it spans over `F`.

## Proof of the restriction-of-scalars statement

The `k`-span `N` of `S` is stable under multiplication by elements of `F`: this is checked by
induction on membership in `N`, using that `S` is `F`-stable and that scalars of `F` commute with
those of `k`. Hence `N` contains the `F`-span of `S`, by induction on membership in the `F`-span.
The other inclusion is immediate since `k`-linear combinations are `F`-linear combinations.
