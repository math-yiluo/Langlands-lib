# Polynomial count of rational matrices of bounded adelic height

`Langlands.Global.GeneralLinearRationalHeightCountStatement` is a
proposition definition. It supplies no proof.

## Statement

For every number field `F` and every positive rank `n` there are a real
constant `C` and a natural exponent `M` such that for every `B ≥ 1` the set
of `g ∈ GL_n(F)` with

`AdelicMatrixHeight.height F n (diag g) ≤ B`

has at most `C · B^M` elements. Here `diag g` is the image of `g` in
`GL_n(A_F)` under `Matrix.GeneralLinearGroup.map` of the diagonal embedding
`algebraMap F (AdeleRing (𝓞 F) F)`. `AdelicMatrixHeight.height` is the
Library's dimension-scaled full adelic matrix-and-inverse height: the
product over finite places of the maximum of the local norms of all
entries of the matrix and its inverse, times the product over infinite
places of `n` times the same maximum, raised to the local degree.

No asymptotic count, embedding independence or statement for a group
scheme other than `GL_n` is asserted.

## Sources and provenance

Internal. The height is that of the published module
`Langlands.Global.AdelicRepresentationHeight`, which follows the doubled
representation of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), (6.3)–(6.4), printed p.158 (registered source
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
The count is the classical finiteness of rational points of bounded height,
made polynomial. It is the lattice-point input for the growth of convolution
kernels on `[G]`, through a faithful matrix representation.

## Intended proof

A private proof compiles. Every entry `x = g i j` satisfies
`mulHeight₁ x ≤ height(diag g)`. At an infinite place `w`,
`max(w x, 1) ≤ n · (local maximum)`, because `w x` is the norm of an entry
of the completed matrix and `n · (local maximum) ≥ 1`. At a finite place,
`max(|x|_v, 1)` is at most the local maximum, which is at least one. The
finite products are compared after reindexing Mathlib's finite places by
`NumberField.FinitePlace.equivHeightOneSpectrum` (`finprod_le_finprod₀`).
So `g` is determined by an `n × n` array of elements of height at most `B`,
and the separately submitted `NumberFieldMulHeightCountStatement` bounds
their number by `C · B^M`. This gives `C^{n²} B^{M n²}`.
