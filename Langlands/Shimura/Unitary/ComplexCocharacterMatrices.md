# Harris cocharacter matrices on every complex test scheme

This module connects the actual Harris cocharacter of `ComplexCocharacter`
to the diagonal formulas of `ComplexMatrixWeights`. It is an internal
consequence of those constructions and the naturality of global sections.
No matrix comparison is supplied as an additional hypothesis.

## Compatible scalars on sections

For any scheme `T` over `Spec ℂ`, write `S = Γ(T, O_T)`.
`AlgebraInvolution.complexTestAlgebra T` is the existing real algebra of
sections obtained by viewing `T` over `Spec ℝ`. The instance
`complexTestAlgebraComplex` equips this same ring with its actual complex
algebra structure from the complex structure morphism of `T`.
`complexTestAlgebraTower` proves that these structures form the scalar tower
`ℝ → ℂ → S`.

The proof identifies the algebra maps with the maps on global sections
composed with the inverses of `ΓSpecIso`. Compatibility then follows from
`Scheme.Hom.comp_appTop` and `Scheme.ΓSpecIso_inv_naturality` for the usual
inclusion `ℝ → ℂ`. The real structure is the existing one used by the
cocharacter's point equivalence, rather than an independently chosen real
algebra structure. No affineness hypothesis on `T` is needed.

## Coordinates of the actual target

Retain the actual number fields and algebra of `CentralSimpleUnitaryData`:
`E` is totally real, `K` is totally complex and quadratic over `E`, and `A`
has the specified compatible `E`, `K`, and rational algebra structures.
The datum `D` supplies the central simple CM algebra with its second-kind
involution. The parameter `C : HarrisSignatureCharts` consists of the actual
compatible real-place matrix charts, the chosen complex embeddings, and the
distinguished real place. In particular, the inherited charts retain their
rank and signature requirements.

`D.complexPointMatrices C T` takes a point of
`D.complexRationalGroupScheme`, the actual iterated pullback from the
rational group to the real and then complex base. It first composes that
point with the complex pullback of `D.realGroupSchemeIso`. The published
`complexSimilitudePointsEquiv` identifies the result with a similitude in
`S ⊗[ℝ] (ℝ ⊗[ℚ] A)`, using `D.rationalBasis.baseChange ℝ` for the real
scheme model. The underlying algebra element is then mapped through
`C.iteratedScalarMatrixEquiv D.totallyRealBasis S`.

The output is a pair of `n × n` matrices over `S` at each real embedding
`τ : E → ℝ`. This is a coordinate function on actual scheme points; it is
not asserted here to be a scheme isomorphism or an equivalence with every
pair of invertible matrices. In particular, the scalar multiplier is not
included in this coordinate function's output.

## Cocharacter formula

Let `x : T → Gm_ℂ`, and let `u` be its corresponding global unit under
`GroupScheme.Gm.pointsEquiv`. Put `rτ = n - 1` at the distinguished real
place and `rτ = n` elsewhere. The theorem `harrisCocharacter_matrices`
computes the matrices of the actual point
`x ≫ (D.harrisCocharacter C first).hom.hom` for either selected source
factor.

For `first = true`, the result is

\[
 \left(\operatorname{diag}(1\text{ for }i<r_\tau;\ u\text{ otherwise}),
       \operatorname{diag}(u\text{ for }i<r_\tau;\ 1\text{ otherwise})\right).
\]

For `first = false`, the two matrices are interchanged. All off-diagonal
entries vanish. Thus the first selected factor has weights zero then one
in the first matrix, and one then zero in the second, in the corrected
Harris convention. These formulas hold on every complex test scheme,
without assumptions that it is affine, reduced, or of finite type.

The implemented proof uses `harrisCocharacter_comparison` to move to the
actual real algebra model, then `ComplexHom.cocharacter_points` to evaluate
the cocharacter. `factorCocharacter_quadratic` identifies its quadratic
unit with the inverse split image of `(u,1)` or `(1,u)`. The two existing
`delignePoints_firstFactor` and `delignePoints_secondFactor` formulas then
supply the matrices, using the scalar tower proved above.

## Provenance and remaining scope

The construction and proof compose existing algebraic maps, point
comparisons and their proven formulas. They introduce no further external
existence theorem and do not alter the inherited Harris convention.
They retain the specified charts and bases. Independence of those choices,
conjugacy, a scheme splitting of the target group, the inverse/conjugated
Kottwitz matrix formula, reflex-field comparison, smoothness and reductivity,
and the PEL geometry, levels and coefficient descent remain separate work.
