# Actual dynamic-parabolic quotient comparison

This internal construction uses the existing actual group scheme, the actual
orbit-extension functor `Dynamic.parabolic χ`, and both existing coset
quotients. The topology on identity-test points is exactly
`rationalPointTopology`. The topology on flag-scheme points is exactly
`schemePointTopology`.

`dynamicParabolicFlagHomeomorph` takes a field `k`, an affine group scheme `G`,
a cocharacter `χ`, an actual relative scheme `Q` and a relative morphism
`π : G.X → Q`. It assumes exact fibers on all test schemes:
`g ≫ π = h ≫ π` if and only if `g⁻¹h ∈ Dynamic.parabolic χ(T)`.
It also assumes `HasOpenSectionsAtPoints k k π`. The topology on `k` need only
have continuous multiplication and `IsOpenUnits k`; properness is not needed
for this topological comparison.

The algebraic-section bridge gives continuous local sections on the actual
scheme-point spaces. The affine source's final topology equals its evaluation
topology. Composing with the published homeomorphism from identity-test to
evaluation points transfers continuity and the local sections to the actual
source convention. Naturality and injectivity of `rationalPointEquiv` turn the
algebraic fiber condition into the existing coset relation. The generic
quotient comparison therefore gives the asserted homeomorphism from the
canonical `gP` quotient onto `Q(k)`. Its representative formula is
`[g] ↦ rationalPointEquiv k G.X g ≫ π`.

`dynamicParabolicQuotientInversion` specializes the generic inversion
homeomorphism to the actual rational points of every connected reductive
group scheme over a topological field whose operations form a topological
ring. Affineness and smoothness come from `IsConnectedReductive`; smoothness
supplies local finite type. The canonical rational-point topological-group
theorem supplies continuous inversion for the existing categorical Hom group
operations. Thus inversion descends from `Pg` classes to `gP` classes in the
two canonical quotient topologies.

`dynamicParabolicQuotientCompact_of_flag_and_proper_points` is conditional.
Its two assumptions are the algebraic
`DynamicFlagQuotientExistenceStatement` and compactness, in
`schemePointTopology`, of every proper scheme's rational points over every
nonarchimedean local field. Applying the first assumption gives the actual
flag model, exact fibers and algebraic sections. Applying the second makes
that model's point space compact. The flag homeomorphism then gives compactness
of the `gP` quotient, and actual inversion gives compactness of the `Pg`
quotient. The conclusion is exactly the unchanged published
`DynamicParabolicQuotientCompactStatement`, at its full universe.

For the local-field application, the existing topological additive group
supplies its compatible uniformity. The valuation then supplies separation,
and the topological division-ring structure supplies continuous inversion
away from zero. Mathlib's field instance therefore gives `IsOpenUnits F`
for the original field topology, without an additional assumption.

The algebraic existence and proper-point compactness assumptions remain
unproved inputs to this helper theorem. This module does not prove the
unconditional compactness target and adds no hypothesis to its definition.
Provenance is internal: it composes the existing point comparisons, the
algebraic-section continuity bridge, and the generic quotient constructions.
