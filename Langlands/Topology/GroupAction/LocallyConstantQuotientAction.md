# Continuous equivariant locally constant quotient descent

Worker 56 constructs continuous equivariant descent for an actual equivariant
quotient map `q : C(X, Y)` between compact action spaces of a topological
group `G`. The original group topology is retained. The coefficient set `A`
has an independent universe and no topology or action.

`FiberCompatible q A` is the subtype of all `DiscreteLocallyConstant X A`
whose values agree whenever their images under the original `q` agree.
`compatibleSmul` restricts the original inverse-precomposition action:
its value at `x` is `f(g⁻¹ • x)`. Equivariance of `q` ensures that inverse
translation sends equal-image pairs to equal-image pairs, proving that
these operators preserve the complete fiber equations. The inherited
action laws give `compatibleAction`. The subtype topology is discrete.
The proved joint continuity of the upstairs discrete function action,
composed with the subtype inclusion, gives `compatibleContinuousAction`.
`compatibleInclusion` is the unchanged continuous equivariant inclusion
into the entire upstairs function space.

`compatiblePullback` uses the original quotient map and supplies its fiber
equations. `compatibleDescend` applies the existing locally constant
quotient descent to the actual upstairs function and its fiber equations.
Its value at `q x` is the original value at `x`. Surjectivity and this
evaluation law prove both inverse laws, including empty spaces and empty
coefficient sets whenever the given functions exist. `compatibleEquiv`
records the resulting function-set equivalence.

`compatibleDescentIso` bundles this equivalence as an isomorphism in
`ContAction TopCat G`. Both directions are continuous because the function
spaces are discrete. The original equivariance equation at `g⁻¹` proves
that pullback intertwines the two action operators; `Action.mkIso` supplies
the inverse equivariance from the inverse laws. No descended function or
fixedness hypothesis is supplied as an input.

This is an internal construction from the existing compact function action,
quotient descent, and the categorical construction of an equivariant
isomorphism. It concerns locally constant functions and complete quotient
fiber equations, and asserts no equivalence of arbitrary sheaf categories
or analytic sites.
