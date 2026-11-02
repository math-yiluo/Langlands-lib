# Polynomial growth relative to an actual algebraic matrix representation

For a number field `F`, an actual group scheme `G` over `F`, and a specified
`rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N)`, the namespace
`Langlands.Global.RepresentationGrowth` constructs a height and a complex
polynomial-growth function space on `InfiniteAdelicGroupPoints F G`. The rank
`N` may be zero. No affine, reductive, faithful-representation or smoothness
hypothesis is required for this construction.

## Actual point map and height

`infiniteMatrix F G rho` is the continuous group homomorphism obtained by
evaluating the actual group-scheme morphism `rho` on the algebra
`InfiniteAdeleRing F` and then applying the existing infinite general-linear
point homeomorphism. Thus its value is the matrix of this specified algebraic
representation, rather than an arbitrary continuous representation supplied
independently of the group scheme.

The definition `height` pulls back the unchanged
`Langlands.Global.ArchimedeanGL.matrixHeight F N` along this homomorphism.
That matrix height is the maximum of one, the mixed-coordinate matrix norm,
and its inverse norm. Its norm conventions are those of
`Langlands/Global/ArchimedeanGrowth`: the finite-product mixed coefficient
norm and matrix operator row-sum norm.

`one_le_height`, `height_nonneg`, `continuous_height`, `height_inv` and
`height_mul_le` prove, respectively, the lower bound by one, nonnegativity,
continuity, equality under inversion, and
`height (g*h) ≤ height g * height h`. The proofs compose the existing matrix
height results with the continuous group homomorphism and its group laws.

## Growth module and action

`HasPolynomialGrowth F G rho f` means exactly

```
∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ g, ‖f g‖ ≤ C * height F G rho g ^ d.
```

It imposes no continuity or smoothness on `f`. The zero function and constant
functions satisfy the condition. Addition takes the sum of the constants and
the maximum of the exponents, using `height ≥ 1`; scalar multiplication
multiplies the constant by the scalar norm. For the positive right translate
`g ↦ f(g*h)`, the proof uses the same exponent `d` and constant
`C * height h ^ d`, by submultiplicativity. Translation by `h⁻¹` proves the
converse in `hasPolynomialGrowth_rightTranslate_iff`.

`polynomialGrowthFunctions` packages these bounds as an actual complex
function submodule. `polynomialGrowthRightAction` is a representation on
its carrier with the exact formula `R(h)f(g)=f(g*h)`. The unit law and
multiplication law follow by evaluating functions and using the group laws;
the action involves no inverse or changed sign.

## Exact standard-representation comparison

For `G = GL_n` and `rho = MatrixRepresentation.standard`, the theorem
`infiniteMatrix_standard` identifies the point map with the original
`GeneralLinearGroupPoints.infiniteHomeomorph F n`.
`height_standard` is exact equality with the original matrix height.
`hasPolynomialGrowth_standard_iff` preserves and reflects the original
`ArchimedeanGL.HasPolynomialGrowth` predicate after transporting functions
through that homeomorphism.

`standardPolynomialGrowthEquiv` gives the resulting complex linear equivalence
with the original `ArchimedeanGL.polynomialGrowthFunctions F n`, with explicit
inverse maps by composition with the point homeomorphism and its inverse.
The inverse laws follow from those of the point homeomorphism. The theorem
`standardPolynomialGrowthEquiv_rightAction` identifies the transported action
pointwise with positive right multiplication by the original matrix point.
No additional topology on these function submodules is asserted.

## Provenance and retained obligations

This is a derived construction from the actual `MatrixRepresentation`,
`affinePointsTarget`, its proved continuity and the existing
`ArchimedeanGrowth` height and bounds. Its closure proofs implement the same
elementary inequalities on this pullback height. It invokes no new external
structural theorem.

The representation is specified and need not be faithful; for example, a
trivial representation gives a constant height. This file does not assert
existence of a faithful algebraic representation or independence of the
growth condition from that choice. It does not identify the height with a
source's global adelic norm, construct differential operators, impose
uniform bounds on derivatives, or prove reduction theory, finite volume,
decay, square-integrability or an automorphic Hilbert-space realization.
Finite-slice automorphic growth and its comparison are further constructions.
