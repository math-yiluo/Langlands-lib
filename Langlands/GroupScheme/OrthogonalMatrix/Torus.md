# The diagonal torus of the split orthogonal group

This internal module defines the diagonal torus of the split orthogonal group
`OrthogonalMatrix.groupScheme l R` and computes its weights on the Lie algebra. It
follows the published module `SymplecticMatrix.Torus` and reuses its pure matrix
facts (`SymplecticMatrix.torusWeights`, `weightCoord`, `prod_zpow_weightCoord_sub`,
`torusWeights_mulSingle`, `levi_diagonalTorusUnits`, `characterValue_eq_prod`,
`isSplitTorus_diagonalTorus`), which do not mention the symplectic group.

## The torus

- `diagonalTorus l R`: the split torus `𝔾ₘ^l` mapped to `O_{2l}` by
  `t ↦ diag(t, t⁻¹)`, the published diagonal torus of `GL_l` followed by the Levi
  embedding `leviMap`.
- `affinePointsEquiv_diagonalTorus_inclusion`: an affine point of the torus, viewed in
  `GL_{l ⊕ l}`, is the diagonal matrix with entries `t_a` at `inl a` and `t_a⁻¹` at
  `inr a` (`torusWeights`).
- `pointsEquiv_diagonalTorus`: the same on arbitrary points.
- `mono_diagonalTorus_hom`: the torus map is a monomorphism, read off from the `inl`
  diagonal entries.

## Over a field `k`

- `isClosedSubgroup_diagonalTorus`, `isSplitSubtorus_diagonalTorus`: the image is a
  closed split subtorus (a monomorphism from a torus is a closed immersion, published
  `IsTorus.isClosedSubgroup_of_mono`).
- `mem_weightSpace_diagonalTorus_iff`: an element `X` of the Lie algebra lies in the
  weight space of a character `χ` exactly when for every `k`-algebra `A`, torus point
  `t` and indices `x, y`, the `(x, y)` entry of `t · lieMatrix X · t⁻¹` equals
  `χ(t)` times the `(x, y)` entry of `lieMatrix X`.
- `mem_weightSpace_diagonalTorus_iff_support`: equivalently, every nonzero entry of
  `lieMatrix X` at `(x, y)` has `χ = w(x) - w(y)` in coordinates, where
  `w(inl a) = e_a` and `w(inr a) = -e_a`. The forward direction tests against the
  generic point `T` of `𝔾ₘ` in one coordinate (Laurent polynomial comparison).

The proofs are those of the symplectic module with the orthogonal model substituted.
