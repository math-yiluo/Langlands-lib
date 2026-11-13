# Smoothness of the split orthogonal group scheme

This internal module proves that `OrthogonalMatrix.groupScheme l R` is smooth over
`Spec R` for every commutative ring `R` (instance `smooth_groupScheme`).

## Infinitesimal lifting

Let `N` be an ideal of a commutative ring `C` with `N ^ 2 = 0`, and let `x` be an
orthogonal matrix over `C ⧸ N`. `exists_map_eq` produces an orthogonal matrix over
`C` reducing to `x`. Write `Q` for `formMatrix`, `J` for `polarMatrix` and
`P = Q J = [[1, 0], [0, 0]]` (`firstProjection`), so that `J Q = 1 - P` and `Pᵀ = P`.
The construction:

1. The defect of `x` is alternating: `defect x = U' - U'ᵀ`. Lift `x` and `U'`
   entrywise to matrices `g` and `U` over `C`. Then
   `ε = defect g - (U - Uᵀ)` reduces to zero, so all its entries lie in `N`
   (`IsSmall N ε`, the Library's `SymplecticMatrix.IsSmall`).
2. Put `E = -ε J`. Products of two matrices with entries in `N` vanish
   (`IsSmall.mul_eq_zero`). Since `g Q gᵀ = Q + (U - Uᵀ) + ε`, expanding
   `(1 + E) g Q gᵀ (1 + Eᵀ) - Q` and dropping the products `E ε`, `ε Eᵀ`, `E Q Eᵀ`,
   `E (U - Uᵀ) Eᵀ` gives
   `(U - Uᵀ) + ε + E Q + Q Eᵀ + E (U - Uᵀ) + (U - Uᵀ) Eᵀ`.
3. Here `E Q = -ε + ε P` and `Q Eᵀ = -P εᵀ`, so the defect equals `W - Wᵀ` for
   `W = U + ε P + E U + U Eᵀ`. Hence `(1 - ε J) g = (1 + E) g` is orthogonal
   (`correction_mem`), and it reduces to `x` because `ε J` reduces to zero.

The argument never divides by `2`, so it works in every characteristic.

## Smoothness

The defining ideal is spanned by finitely many polynomials (`ideal_fg`), so the
coordinate ring is finitely presented over `R`. Through `homEquiv`, the lifting
property is Mathlib's criterion `Algebra.FormallySmooth.of_comp_surjective` for the
coordinate ring, so the coordinate ring is formally smooth and hence smooth
(`smooth_coordinateRing`). The published `Corepresented.smooth_groupScheme_iff` turns
this into smoothness of the structure morphism of the group scheme.

The provenance is elementary: this is the standard infinitesimal-lifting proof that
the orthogonal group of a nondegenerate quadratic form of even rank is smooth,
written with the alternating-defect description so that it does not need `2` to be
invertible. The module states nothing about connectedness or reductivity.
