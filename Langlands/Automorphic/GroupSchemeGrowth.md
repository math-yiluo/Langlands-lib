# Polynomial growth on actual adelic rational-function slices

For a number field `F`, an actual affine group scheme `G` over `F`, and a
specified algebraic matrix representation `rho` of finite rank, this module
constructs polynomial-growth subspaces of the existing
`GroupSchemeFunctions.ContinuousRationalFunctions F G`. These are actual
continuous complex functions on the full adelic point group, invariant under
the actual principal rational-point map. They are not required here to
descend through a split-centre quotient.

## Actual slices and full right action

`HasPolynomialGrowth F G rho f` means that every fixed finite-adelic slice
`infiniteSlice F G b f` satisfies
`RepresentationGrowth.HasPolynomialGrowth F G rho`. Equivalently, for every
finite point `b` there exist `C ≥ 0` and `d : ℕ` such that at every infinite
point `a`,

```
‖evaluate F G f (AdelicGroupPoints.pair F G a b)‖
  ≤ C * RepresentationGrowth.height F G rho a ^ d.
```

The constant and exponent may both depend on `b`. The height is the pullback
of the original matrix-and-inverse height along the actual infinite-point
map of `rho`, as constructed in `Langlands.Global.RepresentationGrowth`.

`polynomialGrowthSubrepresentation` is the intersection of the inverse
images of that growth submodule under the actual complex linear slice maps.
`mem_polynomialGrowthSubrepresentation` identifies membership exactly with
the displayed predicate.

For a full adelic right translate by `g`, the slice at `b` becomes the
positive infinite right translate by `infinite g` of the original slice at
`b * finite g`. The proof uses the existing exact identity
`AdelicGroupPoints.pair_mul_right` and the proved infinite growth
translation bound. This proves stability under the existing full positive
right action, without a uniform bound as `b` varies.

`PolynomialGrowthRationalFunctions` is the carrier of this subrepresentation,
and `polynomialGrowthRightAction` is its restricted representation.
`polynomialGrowthInclusion` is an injective intertwining map into the
continuous rational-function representation. The evaluation formula remains
exactly `R(g)f(x)=f(x*g)`.

## Smooth and common-stabilizer intersections

`plotSmoothPolynomialGrowthSubrepresentation` intersects this growth
condition with the existing infinite plot-smooth and finite-slice locally
constant space. `finitePlotSmoothPolynomialGrowthSubrepresentation`
intersects growth with the existing infinite plot-smooth space having one
common open stabilizer in the finite factor. Both are full adelic
subrepresentations by their construction as intersections.

The common-stabilizer intersection is contained in the finite-slice
intersection. The proof applies the existing inclusion of the corresponding
smooth subrepresentations and takes the intersection with growth.
No equivalence between finite-slice local constancy and a common stabilizer
is asserted.

## Exact original general-linear comparisons

Take `G = GL_n` and `rho = MatrixRepresentation.standard`.
`continuousGeneralLinearEquiv_mem_polynomialGrowth` preserves and reflects
membership in the original
`Langlands.Automorphic.polynomialGrowthSubrepresentation F n`. Its proof
uses the existing exact slice comparison, the standard-representation
height/growth comparison and surjectivity of the finite point
homeomorphism.

`polynomialGrowthGeneralLinearEquiv` restricts the unchanged
`continuousGeneralLinearEquiv` to a complex linear equivalence onto the
original `Langlands.Automorphic.PolynomialGrowthRationalFunctions F n`.
Its explicit inverse is the restriction of the ambient inverse, with
membership proved by the same equivalence of predicates. The inverse and
linear laws are inherited by subtype extensionality. The comparison commutes
with the faithful ambient inclusions and intertwines the exact restricted
full positive right actions.

The two additional membership comparisons combine this result with the
already proved smooth and common-stabilizer membership comparisons.
`plotSmoothPolynomialGrowthGeneralLinearEquiv` and
`finitePlotSmoothPolynomialGrowthGeneralLinearEquiv` give explicit complex
linear equivalences with the unchanged original
`smoothPolynomialGrowthSubrepresentation` and
`finiteSmoothPolynomialGrowthSubrepresentation` carriers. Each equivalence
intertwines the restricted full positive right representations by the
existing ambient action identity. No topology on these growth carriers or
topological equivalence between them is asserted.

## Provenance and retained obligations

This is a derived construction using the existing actual finite/infinite
factorization, slice maps, smooth subrepresentations, ambient GL comparison
and the specified-representation height and growth bounds. The standard
comparison preserves the original matrix spaces, heights and positive
action. No new external structural theorem is invoked.

Growth is relative to the supplied representation and is separately
quantified on each finite slice. Faithful representation existence,
independence of its choice, comparison with a global adelic norm and
uniform differential moderate growth remain obligations. This module
constructs no differential operators and imposes no bounds on their
derivatives. It proves no reduction theory, finite-volume, rapid-decay,
square-integrability or automorphic Hilbert-space identification theorem.
