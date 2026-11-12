# Smoothness of the split symplectic group scheme

This internal module proves that `SymplecticMatrix.groupScheme l R` is smooth over
`Spec R` for every commutative ring `R` (instance `smooth_groupScheme`).

## Infinitesimal lifting

Let `N` be an ideal of a commutative ring `C` with `N ^ 2 = 0`, and let `x` be a
symplectic matrix over `C ⧸ N`. `exists_map_eq` produces a symplectic matrix over `C`
reducing to `x`. The construction:

1. Lift `x` entrywise to an arbitrary matrix `g` over `C`. The defect
   `ε = g J gᵀ - J` reduces to zero, so all its entries lie in `N`
   (`IsSmall N ε`).
2. `ε` is alternating: `εᵀ = -ε` because `Jᵀ = -J`, and its diagonal vanishes
   because the diagonal of every `A J Aᵀ` vanishes
   (`mul_J_mul_transpose_apply_self`, a direct computation with the blocks of `J`).
   The diagonal statement matters in characteristic two.
3. Let `U = strictUpper ε` be the strictly upper triangular part of `ε`, for the
   order of the indices given by `Fintype.equivFin`. Then `U - Uᵀ = ε`
   (`strictUpper_sub_transpose`).
4. Put `E = U J`. Products of two matrices with entries in `N` vanish
   (`IsSmall.mul_eq_zero`). Expanding `(1 + E)(J + ε)(1 + Eᵀ)` and using
   `J J = -1`, `E J = -U` and `J Eᵀ = Uᵀ`, the expression equals
   `J + ε - U + Uᵀ = J`. So `(1 + E) g` is symplectic (`correction_mem`), and it
   reduces to `x` because `E` reduces to zero.

## Smoothness

The defining ideal is spanned by finitely many entries (`ideal_fg`), so the
coordinate ring is finitely presented over `R`. Through `homEquiv`, the lifting
property is Mathlib's criterion `Algebra.FormallySmooth.of_comp_surjective` for the
coordinate ring, so the coordinate ring is formally smooth and hence smooth
(`smooth_coordinateRing`). The published `Corepresented.smooth_groupScheme_iff`
turns this into smoothness of the structure morphism of the group scheme.

The provenance is elementary: the correction step is the standard proof that the
symplectic group is smooth, written so that it does not need `2` to be
invertible. The module states nothing about connectedness or reductivity.
