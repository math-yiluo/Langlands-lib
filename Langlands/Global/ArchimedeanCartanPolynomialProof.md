# The finite joint-orbit annihilator for the actual Cartan square sum

This proof specializes the published statement in
`Langlands.Global.ArchimedeanCartanPolynomialStatement`. Its statement pair
and imports remain unchanged. The generic theorem `jointOrbitPolynomialAnnihilation` is imported from
`Langlands.Global.ArchimedeanJointPolynomialProof`. The actual Casimir,
trace-form and Cartan decomposition are imported from their published
modules. Worker 94 developed this internal algebraic specialization;
Worker 88 checked the published inputs and prepared the focused proof
contribution.

`cartanSquareSumPolynomialAnnihilation` proves precisely
`CartanSquareSumPolynomialAnnihilationStatement K n`. Given an actual
joint-finite smooth function `f`, it applies
`jointOrbitPolynomialAnnihilation` to the central element
`matrixCentralCasimir K n` and the compact-enveloping element
`(2 : ℂ) • compactCartanElement K n`. The generic result supplies a
single monic polynomial of degree the dimension of the joint orbit,
annihilating every vector in that orbit.

Scalar multiplication in the compact subalgebra has the original
scalar-multiplied value in the ambient enveloping algebra.
`cartanSquareSum_eq_central_add_compact` therefore identifies the
generic central-plus-compact argument exactly with `cartanSquareSum`.
Rewriting this identity under polynomial evaluation and the genuine
enveloping action gives the required annihilation for every orbit
vector. The polynomial, its monicity and its degree are unchanged.

The argument is an internal algebraic specialization and adds no
hypotheses. It retains arbitrary number-field universe, every natural
rank, the zero orbit and the degree-zero case. It proves no
ellipticity of the polynomial differential operator, analytic
regularity, analyticity, jet uniqueness, reproduction or final
automorphic derivative growth.
