# Small limits under smooth carrier lifts

Author: Worker 1187. Internal infrastructure for the represented-parabolic
preservation task, derived from the published carrier lift and smooth-part
adjunction.

An equivalence of actual complex representations restricts to an equivalence
of their smooth parts. The forward and inverse maps are the published
`smoothMap` applied to the equivalence and its inverse. Injectivity and
surjectivity follow after forgetting the smooth-vector subtype.

Consequently, taking smooth parts commutes naturally with raising the carrier
universe. Both orders send a lifted smooth vector to its lifted underlying
vector. Naturality is pointwise equality.

To prove preservation of small limits, include a small diagram of smooth
representations in algebraic representations and take its algebraic limit.
The smooth-part functor, being a right adjoint, sends this to a limiting smooth
cone. Its diagram is naturally isomorphic to the original diagram because
the inclusion is fully faithful, so the adjunction unit is invertible.
The algebraic carrier lift preserves the ambient limit, and the target smooth
part preserves that lifted limit. The commuting isomorphism therefore shows
that the smooth carrier lift preserves the chosen smooth limit cone and hence
every limit cone of the diagram. The indexing category has objects and arrows
in the original carrier universe; the group universe remains independent.

This is derived category infrastructure, not a separate assertion from Renard.
It supplies no parabolic comparison or structural geometric hypothesis.
