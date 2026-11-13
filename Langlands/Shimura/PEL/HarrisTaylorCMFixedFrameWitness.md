# Actual frame witnesses for a fixed Harris level orbit

This module defines the internal predicate `OriginalLevelFrameWitness` and proves
`exists_frame_original_element_of_levelIso_fixed`. It is a structural step toward
`CMSmallLevelRigidityStatement`; it does not prove small-level rigidity.

For the original Harris datum `D`, signature charts `C`, and a positive polarized
action object `X`, the predicate takes an original Harris level `U`, a rational
unit `q`, an actual rational action self-isomorphism `e`, and its actual
polarization-multiple equation `he`. It asserts the existence of an actual
Weil-compatible adelic frame `eta` and an element `u` of `U.subgroup` such that
transporting `eta` by `e` is right translation of `eta` by the scalar-extension
image of `u`. The right action is source precomposition. The group containing
`u` is the original opposite finite adelic similitude group of `D`, rather than
an abstract replacement group.

The theorem starts with an actual monodromy-invariant orbit `a` at the transported
Harris level and assumes that the existing `PolarizedWeilLevel.levelIso` fixes
`a`. All tensor, Picard, finite Weil, dual-scheme, polarization, Tate, and geometric
point data are exactly the data of the imported actual level construction. The
predicate itself does not require orbit invariance or existence of a fixed orbit;
those enter in the theorem's premise. No smallness, finite-order, finiteness, or
faithfulness hypothesis is used or inferred here.

The implemented proof chooses a quotient representative of `a.val`, forgets the
fixed-point subtype in the equality, and unfolds level transport as the existing
right-equivariant map on frame orbits. `RightOrbit.mk_eq_mk` supplies an element
of the transported subgroup whose source translation is the isogeny transport
of that frame. The inverse of
`harrisFiniteAdelicScalarExtensionContinuousEquiv` recovers the original element
`u`; `hodgeLevelFunctor_obj_mem` recovers its original subgroup membership. The
continuous group equivalence's inverse law gives the required frame equation.

This is an internal construction and derived quotient argument from the published
`InvariantOrbits`, `OrbitTransport`, `WeilLevelIsogeny`, and Harris level transport
definitions. It introduces no assertion attributed to external literature. The
remaining rigidity proof must still establish finite order for the resulting
level element, compare its image at the small place with the actual Tate action,
and use the required one-prime faithfulness result.
