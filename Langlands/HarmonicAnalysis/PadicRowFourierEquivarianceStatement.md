# P-adic row Fourier equivariance under general linear substitutions

Worker 455 authored this derived statement with Worker 364's supplied target,
source locator and dependency analysis. It is a Prop-valued definition, with
no proof:
`Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceStatement.{uF} F T d`.
The implicit parameters are a prime `p` and `[Fact p.Prime]`; the explicit
parameters are `F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and
`d : ℕ`. The field universe `uF` is independent.

The definition installs exactly `T.topology`, `T.valuativeRel` and
`T.localField`, then the Borel measurable space of that supplied field topology
and its Borel certificate. The row space carries its product topology and
the finite product of the scalar measurable spaces, as used by the unchanged
`rowMeasure` and `rowFourierIntegral` definitions. There is no alternative
field realization or measure construction in this module.

For every `ψ : UnitaryAdditiveCharacter F.Carrier`, every supplied
`ν : AdditiveHaarMeasure F.Carrier`, every
`g : Langlands.GeneralLinear d F.Carrier`, and every actual
`Φ : SchwartzBruhat (Fin d → F.Carrier)`, the proposition asserts both:

- There exists an actual Schwartz–Bruhat function `Φg` satisfying
  `Φg x = Φ (Matrix.vecMul x g.val)` for every row `x`.
- Every Schwartz–Bruhat function with that pointwise pullback property satisfies,
  for every row `y`,

  ```text
  rowFourierIntegral ψ ν d Φg y =
    ((T.normalizedAbs (Matrix.det g.val) : ℂ)⁻¹) *
      rowFourierIntegral ψ ν d Φ
        (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)).
  ```

Thus the universal formula is accompanied by existence of its test-function
input. Both functions are the existing locally constant, compactly supported
complex functions, rather than arbitrary functions with a presumed
Schwartz–Bruhat certificate.

The integral is the actual plus-sign integral
`∫ x, ψ.complex (∑ i, x i * y i) * Φ x ∂rowMeasure ν d`.
It uses the product of the same supplied scalar Haar measure in every
coordinate. The character type includes continuity, nontriviality and values
in the unit circle. Regularity and the additive Haar property are bundled in
the supplied measure. The statement assumes no scalar self-duality, Fourier
closure, Fourier inversion, scalar Haar scaling, or determinant Haar scaling.
It imposes no preferred normalization on `ν`.

Here rows act on matrices on the right. With `z = xg`, the bilinear pairing
obeys
`rowPairing (z g⁻¹) y = rowPairing z (y (g⁻¹)ᵗ)`.
This accounts for the inverse transpose and introduces neither a minus sign
nor complex conjugation. The Jacobian contributes the reciprocal
residue-normalized determinant absolute value. The factor uses
`T.normalizedAbs`, whose value on a nonzero scalar is
`q ^ (-T.ord x)` for the actual residue cardinality `q`; it does not substitute
the spectral norm without its normalization adjustment. Rescaling the scalar
Haar measure rescales both row Fourier integrals equally, so this identity
does not require the self-invariant normalization used in the source.

Dimension zero is included explicitly by the unrestricted natural parameter
`d`. The empty row space is a singleton, `rowMeasure ν 0` is unit point mass
by `rowMeasure_zero`, the empty determinant is one, and the row pairing is
zero. Hence the determinant factor is one and the asserted transform identity
reduces to the same function value on each side, independently of `ν`.
This zero-dimensional inclusion is part of the internal formulation.

The original source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), §2.10, printed p.396, the unnumbered
Fourier identity between (2.10.2) and (2.10.3). Its conventions are in §0.3:
printed p.375 permits general nonarchimedean local fields; p.376 defines
`g` with superscript iota as the inverse transpose; p.377 uses right
translations; and p.378 defines the plus-sign Fourier integral with
self-invariant Haar measure. These pages were inspected visually in the
registered original `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Their one-based PDF pages are 10–13 and 31.

The p.396 scan appears to place a duplicated Fourier hat on the final `Φ`
on the right of that identity. This is an apparent printing issue: the
change-of-variables formula has a single Fourier transform of `Φ` there.
The Lean formula states that single-transform identity explicitly. No
source-specific `notes/errata/jpss-1983-rankin-selberg.md` was found in the
checked workspace, private notes, project notes/wiki, or pinned Library notes
locations; this records the bounded errata check, not a claim that no errata
exist elsewhere.

This target is a derived p-adic specialization and arbitrary-Haar formulation
of the source identity, with explicit Schwartz pullback existence and dimension
zero. It is not a claim that JPSS states this exact Lean interface. A later
proof can use the published `rowTranslate` construction in the module
`Langlands.HarmonicAnalysis.RowSchwartzAction` and
`rowTranslate_apply` for the required Schwartz pullback, and
`eq_rowTranslate_iff` to identify every pointwise realization. It must also
apply change of variables to the actual product measure. The published
`productMeasure_map_matrix` and
`haarMeasure_map_matrix` in `PadicRectangularHaarScalingProof` use column
multiplication `Matrix.toLin'`; transposing the matrix yields the right row
action. Together with `padicScalarHaarScaling`, they give an available route
to deriving the modulus, rather than adding it as a hypothesis. This module
proves none of those steps and uses no gamma, epsilon or uniqueness theorem.
