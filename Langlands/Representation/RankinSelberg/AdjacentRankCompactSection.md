# Smooth induced sections from the compact adjacent-rank average

This module continues the internal algebraic construction of the inner vector
integral in JPSS Section 6.1, formula (10), printed page 430 of the registered
original `jpss-1983-rankin-selberg`.

Let `K` be a Hausdorff topological field with continuous field operations and
`n` any natural number, including zero. On `GL_n(K)` fix a measurable space
in which open sets are measurable and a measure `μ` finite on compact sets.
Let `ρ` be a smooth representation on an algebraic complex module `V`, let `ξ`
be a unit-valued group character with locally constant complex values, and let
`Φ` be a rectangular Schwartz test with full-row-rank topological support.
No norm or topology on `V` is required. All averages below use this fixed `μ`.

The average is bilinear in the full-rank rectangular test and the representation
vector. Ambient right translation is precisely rectangular right translation
of the test. If `[h,0]p=[ha,0]` and right multiplication by `a` preserves the
chosen measure, then changing variables gives
`A(p g)=ξ(a⁻¹) ρ(a) A(g)`. The proof is a change of variables in the finite
algebraic integral; the matrix identity and measure preservation are explicit
hypotheses of this result.

Let `θ` be a unit-valued character of the ambient `GL_(n+1)(K)` whose kernel is
open. The actual weighted formula is `f(g)=θ(g) A(g)`. Its uniform open right
stabilizer is the intersection of an open stabilizer of `Φ`, supplied by
`RectangularTestSmooth`, with the kernel of `θ`. The same subgroup fixes `f`
at every ambient group point.

More precisely, take any subgroup `P` of the ambient group and a homomorphism
`a : P → GL_n(K)` such that `[h,0]p=[h a(p),0]` for every `h,p`, and assume
right multiplication by each `a(p)` preserves `μ`. Define the representation
of `P` on `V` by
`τ(p)v = θ(p) ξ(a(p))⁻¹ ρ(a(p))v`.
The proved covariance and uniform right stabilizer construct an actual element
of `Induction.SmoothFunctions P τ`, with the displayed value at every `g`.
Thus this is a smooth induced function for the specified subgroup and inducing
representation. The module does not yet identify `τ` with the normalized
opposite-parabolic induction in the host statement.

The actual induced section is bilinear in `Φ` and `v`, so the universal property
of the algebraic tensor product gives a linear section map. Right translation
by `k` sends the section for `Φ,v` to `θ(k)` times the section for `R_k Φ,v`.
These equalities follow by evaluation and the corresponding finite-average
identities.

The generic character formulation and finite-integration proof are internal
derived content motivated by JPSS (10). The exact normalized lower-parabolic
specialization, section spanning, Jacquet identity and closed host image theorem
remain open.
