# Small colimits under normalized Jacquet restriction

Author: Worker 1187. Internal category infrastructure for the Jacquet clause of
Renard VI.1.2 Corollary, proved for the published normalized functor and then
transported to actual Levi points.

The forgetful functor from smooth complex representations to modules preserves
colimits at the original carrier size: the inclusion into algebraic
representations is left adjoint to the smooth part, and the algebraic
representation forgetful functor preserves these colimits. Both forgetful
steps reflect colimits. Scalar twists and pullbacks along topological group
equivalences leave the underlying modules and linear maps unchanged; the same
forgetful argument proves their colimit preservation.

After forgetting the Levi action, normalized Jacquet restriction is naturally
isomorphic to including the smooth representation in algebraic
representations, restricting to the radical subgroup, and taking ordinary
coinvariants. The component is the published `Localization.trivialEquiv`, with
its action forgotten. It identifies the actual localization-at-one relation
quotient with Mathlib's coinvariant quotient. The normalization twist leaves
the underlying module unchanged. Naturality follows by evaluating a quotient
class represented by an original vector.

Algebraic restriction preserves colimits, and ordinary coinvariants are left
adjoint to the trivial-action functor. Their composite therefore preserves
small colimits. Reflection by the target smooth-to-module forgetful functor
establishes `normalizedJacquetFunctor_preservesColimits`. Pullback through the
published Levi-point topological group equivalence gives
`leviJacquetFunctor_preservesColimits` for every actual represented parabolic
and matching Levi/radical datum, without an added unimodularity,
compact-subgroup-limit, or compact-quotient premise. Diagram objects and arrows
remain in the original carrier universe, independent of the field/group
universe.

This module establishes only the Jacquet colimit clause. It supplies neither
induction preservation clause nor the conjunction defined by
`LeviParabolicFunctorsPreserveLimitsStatement`. Its constructions are derived
category infrastructure, not a new translation of a separate source assertion.

Worker 1751's naming repair gives the local represented-parabolic point
topology instance the explicit name
`jacquetColimitsRepresentedPointTopology`. This prevents a generated-name
collision with `RepresentedStandardCuspidality` during combined import and
kernel replay. Its topology and all mathematical declarations are unchanged.
