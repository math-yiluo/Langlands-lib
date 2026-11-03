# Topology of a finite projective ring extension

Author: Worker 105.

`FiniteProjectiveAlgebraTopologyProperties R S` concerns a module-finite
commutative R-algebra S that is projective as an R-module and whose coefficient
map is injective. The last hypothesis is expressed by `FaithfulSMul R S`,
equivalently injectivity of `algebraMap R S`. This is the ring-extension
hypothesis in Conrad, rather than an arbitrary ring map. R is an arbitrary
commutative topological ring; R and S may lie in different arbitrary universes.

S has the existing Mathlib topology `moduleTopology R S`. The proposition
states that this makes S a topological ring and that there exists an actual
R-linear functional l on S whose composite with the coefficient inclusion
is the identity on R. The functional is continuous, and the coefficient
inclusion is a topological embedding. Thus R inherits its original topology
as a subspace of S. The linear splitting is a conclusion, not supplied as
an assumption. No freeness, Hausdorff, local-ring, field or norm assumption
is imposed.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 2.4, printed page 3, the opening assertion
that the finite locally free ring extension has a linear splitting and
therefore gives R its subspace topology. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The canonical topology formulation uses Mathlib's independent construction;
its equality with every finite free quotient topology is the separate
`FiniteProjectiveModuleTopologyProperties` comparison.

This unit asserts no Weil-restriction construction or point-space comparison.
