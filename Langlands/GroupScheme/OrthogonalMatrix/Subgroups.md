# Levi and unipotent subgroups of the split orthogonal group

This internal module provides the matrices and homomorphisms of group schemes used
to produce points of the identity component of the split orthogonal group
`OrthogonalMatrix.groupScheme l R` (Gram matrix `Q = [[0, 1], [0, 0]]` on `l ⊕ l`).

## Matrices

It reuses the block matrices of the published symplectic model:
`SymplecticMatrix.levi A = diag(A, A⁻ᵀ)` for `A ∈ GL_l`,
`SymplecticMatrix.upper Y = [[1, Y], [0, 1]]` and
`SymplecticMatrix.lower Y = [[1, 0], [Y, 1]]`.

- `levi_mem`: `diag(A, A⁻ᵀ) Q diag(A, A⁻ᵀ)ᵀ = Q`, so the defect is zero.
- `upper_mem`: for an alternating `Y` (`IsAlt Y`, i.e. `Y = U - Uᵀ`), the defect of
  `upper Y` is `fromBlocks Yᵀ 0 0 0`, which is alternating.
- `lower_mem`: for an alternating `Y`, the defect of `lower Y` is
  `fromBlocks 0 0 0 Y`, which is alternating.
- Small closure facts: `IsAlt.transpose`, `IsAlt.smul`, `isAlt_fromBlocks₁₁`,
  `isAlt_fromBlocks₂₂`.

## Homomorphisms of group schemes

`leviHom`, `upperHom hY φ` and `lowerHom hY φ` are the group homomorphisms
`GL_l(A) → O(A)`, `t ↦ upper (t • φ(Y))` and `t ↦ lower (t • φ(Y))` (the latter two on
`Multiplicative (Fin 1 → A)`, the points of `𝔾ₐ`). They are natural in the algebra
(`leviTrans`, `upperTrans`, `lowerTrans`) and therefore define homomorphisms of group
schemes `leviMap : GL_l → O_{2l}` and `upperMap hY, lowerMap hY : 𝔾ₐ → O_{2l}` through
the corepresentability API `Corepresented.groupSchemeMap`. The lemmas
`pointsEquiv_leviMap`, `pointsEquiv_upperMap` and `pointsEquiv_lowerMap` compute them
on points.

## Points of the identity component

Over a field `K`, `isAffineHom_groupScheme_of` and `smooth_groupScheme_of` restate the
instances for the base `CommRingCat.of K`. For a matrix `g ∈ O(K)`, `constantPoint T g`
is the point of `O_{2l}` over `T` whose matrix is `g` mapped into `Γ(T, ⊤)`.
`constantPoint_levi_mem`, `constantPoint_upper_mem` and `constantPoint_lower_mem` show
that the constant points of `diag(A, A⁻ᵀ)`, `upper Y` and `lower Y` (`Y` alternating)
lie in the range of `identityComponentι`: they factor through `GL_l` or `𝔾ₐ`, which are
connected, so the published `SymplecticMatrix.comp_mem_range_identityComponentι`
applies.

These are the standard Levi subgroup and unipotent radicals of the Siegel parabolic
subgroups of the split orthogonal group. Beyond these memberships, the module proves
nothing about the identity component.
