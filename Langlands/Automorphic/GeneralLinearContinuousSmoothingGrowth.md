# Moderate growth of smoothed positive-quotient representatives on GL

`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearContinuousSmoothingGrowthStatement`
is an implication from `GroupSchemeQuotientL2ContinuousRepresentativeStatement`.
For the actual adelic point group of `GL_n` and a central split torus with
injective finite-index character restriction, it uses the same quotient,
measures and integrated right action. For a compactly supported continuous
weight `f` and a quotient `L²` vector `φ`, the conclusion gives a continuous
representative `ψ` of the integrated class. For every fixed finite matrix
coordinate `b`, this representative satisfies

\[
\bigl\|\psi(H\,(a,b))\bigr\| \le C_b\,
   \bigl(\texttt{infiniteAdelicHilbertNorm}\ F\ n\ a\bigr)^d,
\qquad d=\dim_{\mathbb R}(\texttt{ArchimedeanMatrix}\ F\ n).
\]

Here `H` is the positive-rational subgroup, `(a,b)` is transported to the
actual adelic point group, and `C_b ≥ 0` need not be uniform in `b`. This is
the growth inequality used on each slice in `isAutomorphicForm_iff_source_conditions`
when the representative is pulled back to the matrix group.

## Implemented proof

The helper `generalLinear_sliceGrowth_of_compactConjugateBound` proves the
estimate whenever the square of the norm of the quotient value at `H x` is
bounded by a nonnegative constant `L` times the canonical subgroup mass of
`H ∩ x S x⁻¹`, for a fixed compact set `S`. The polynomial mass bound gives
`L * B` times the height to the power `2d`. Taking the nonnegative square
root gives `C_b = sqrt (L * B)` and exponent `d`.

For convolution, continuity and compactness bound the kernel on its support,
and it is zero elsewhere. Thus a nonnegative global bound `M` is available.
The assumed representative theorem supplies continuity, equality almost
everywhere with the integrated class and the squared norm estimate. The set
`S` is the product of the topological support of `f` and its inverse, hence
compact. Take `L = M * (∫ ‖f‖) * ‖φ‖²`, regroup the scalar factors of the
squared norm estimate, and apply the helper.

## Provenance and scope

This is a derived consequence of the Library's compact-convolution
representative estimate and the polynomial positive-rational subgroup mass
bound. Its purpose is the moderate growth step for constructing forms from
Hilbert summands, in the context of Getz–Hahn, *An Introduction to Automorphic
Representations*, Springer GTM 300 (2024), Theorem 9.7.3, pp. 265–267 (PDF
pp. 277–279). It does not derive the representative assertion independently,
claim rapid decrease, or prove smoothness, finite-level or finite-type
conditions, density, or irreducibility.
