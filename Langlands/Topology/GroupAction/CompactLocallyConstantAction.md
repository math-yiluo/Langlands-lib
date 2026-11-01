# Discrete continuous actions on locally constant functions

Worker 56 constructs `DiscreteLocallyConstant X A`, a wrapper equivalent to
Mathlib's actual locally constant functions from the topological space `X`
to the arbitrary coefficient set `A`. It carries the discrete topology.
No action or topology on `A` is supplied. The domain, group and coefficients
have independent universes. The wrapper distinguishes domain
precomposition from Mathlib's pointwise coefficient action.

For a group action on `X` with continuous operators for each fixed group
element, the function action is `(g • f)(x) = f(g⁻¹ • x)`. Local constancy
is preserved by continuous precomposition. The inverse and action laws prove
the group action laws. `stabilizer_eq` proves that its entire stabilizer is
exactly `CompactAction.functionStabilizer G f`: the equation with `g⁻¹`
is equivalent to the equation with `g` by evaluating at `g • x` or
`g⁻¹ • x`.

When `G` is a topological group acting jointly continuously on a compact
space `X`, the previously published `functionStabilizer_isOpen` supplies
openness of every function stabilizer. Mathlib's
`continuousSMul_iff_stabilizer_isOpen` then proves joint continuity on the
entire discrete function space. `continuousAction` bundles it in
`ContAction TopCat G`. The group retains its supplied topology. Neither
Hausdorffness of `X`, local compactness of `G`, nor nonemptiness is required.

`pullback` uses the original continuous domain map. A surjective map gives
an injective pullback by evaluation at a preimage. For an equivariant map,
`pullback_smul` proves equivariance of inverse precomposition by evaluating
the original domain equivariance equation at `g⁻¹`.

This is an internal construction from continuous precomposition, group
action laws, the published compact-action stabilizer theorem and Mathlib's
discrete-action continuity criterion. It supplies constant-coefficient
local function data for actual compact represented analytic domains.
It does not construct an arbitrary equivariant sheaf, a representation
category or a cohomological comparison.
