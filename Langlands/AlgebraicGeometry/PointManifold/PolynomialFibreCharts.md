# Charts on polynomial solution spaces

This internal helper constructs a local chart on a finite polynomial solution space over an `RCLike` field `k`. The variables are indexed by `τ ⊕ σ`, with `τ` the free variables and `σ` the dependent variables and also the relation indices. Both types are finite, including the empty cases.

For relations `p`, `polynomialRelations p x` is their simultaneous evaluation. The ambient `polynomialCoordinateMap p x` pairs the free coordinates of `x` with those evaluations. The matrix `polynomialRelationJacobian p x` has relations as rows and dependent variables as columns; its entries are the evaluations of formal partial derivatives.

`polynomialCoordinateDerivative` pairs the free-coordinate projection with the derivatives from `PolynomialCalculus`. The module proves that this is the Fréchet derivative of the ambient map and that the ambient map is smooth at every order. When the dependent Jacobian has nonzero determinant, a vector in the derivative's kernel has zero free coordinates, and its dependent coordinates are annihilated by this nonsingular matrix. Thus the derivative is injective. Equality of finite dimensions gives surjectivity, yielding `polynomialCoordinateDerivativeEquiv`.

Given nonsingularity at every solution and a chosen solution `x₀`, `polynomialFibreChart` applies the smooth inverse function theorem to the ambient map at `x₀`, then restricts it with `zeroFibreChart`. Its source contains `x₀`. Its forward map on the entire solution subtype is exactly the free-coordinate projection. The solution subtype carries the topology induced from the finite product of copies of `k`.

`polynomialFibreChart_contDiffOn_symm_val` proves smoothness over `k` of the inverse chart followed by inclusion into the ambient variable space on the whole chart target. It uses invertibility of the derivative at every solution in the source, through `zeroFibreChart_contDiffOn_symm_val`. The final theorem composes this inclusion with polynomial evaluation, proving smoothness of every polynomial evaluation along the inverse chart. These are assertions of smoothness over `k`; the actual-point chart application still needs identification with algebraic points and restriction of scalars to the reals.

The construction is derived internally from the pinned Mathlib finite-dimensional linear algebra and calculus APIs, together with the internal `PolynomialCalculus` and `ZeroFibreChart` helpers. It is a prerequisite for regular chart existence and does not itself identify the solution subtype with scheme points or prove the host target.
