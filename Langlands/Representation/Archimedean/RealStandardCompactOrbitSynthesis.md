# Compact convolution of translates of real standard vectors

The module defines the injective continuous-profile map `compactFiniteProfile`
on the algebraic compact-finite source of a real standard module.
`translatedSeedProfile` is the restriction of `b R(g)v` to the orthogonal group
in the compact Banach model.

`realStandardCompactOrbitSynthesis` proves `RealStandardCompactOrbitSynthesisStatement`.
For every jointly continuous Banach representation and compact and Lie intertwiner
`f` from the algebraic source into its smooth vectors, left convolution of the
profile of `w` by `translatedSeedProfile ds b g v` is the profile of a vector `z`
of that same algebraic source. Its image satisfies

\[
\|f(z)\| \le C\,\operatorname{height}(g)^d\,|b|\,\|f(v)\|\,\|w|_{O(n)}\|_\infty,
\]

where the norms of `f(z)` and `f(v)` use underlying Banach evaluation.
The measure is a left- and inversion-invariant Borel probability measure on
`O(n)`. The constants are independent of the seed, the input, the scalar, and
the translate.

The function `k ↦ w(k⁻¹)` lies in a finite-dimensional left translation space
obtained from the compact orbit span of `w`. Apply
`realSmoothCompactWeightedTransfer_orthogonal` with this weight to the scaled
seed. Pointwise evaluation and Haar inversion identify the source integral
with left convolution. The target integral is bounded by moderate growth and
the uniform bound on the height of a compact matrix. The translated seed and
its integral are handled by the actual full-group actions on the Banach spaces.
