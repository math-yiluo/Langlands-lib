# Comparing the two compact-section constructions

Author: Worker 13.

This internal comparison connects `LocalCompactSections`, which defines support
by actual zero neighbourhood restrictions, to the existing `CompactSections`
construction using nonzero stalk germs. The space `X`, commutative ring `R`
and module carriers lie in `Type u`, as required by the existing stalk API.
The group `G` lies independently in `Type v`. Each spatial group operator is
continuous (`ContinuousConstSMul G X`). The group needs no topology, and the
coefficients need no topology.

`stalkLinearEquiv F` applies to every module presheaf on the labelled-open
category. Its forward and inverse maps retain the exact underlying global
section. The imported theorem `LocalSupport.support_eq_stalkSupport` proves
that the two actual supports are equal, so the full compact-support conditions
are equivalent. The subtype maps are additive, scalar-linear and mutually
inverse by their definitions.

`stalkEquiv F` is the resulting representation equivalence, and `stalkRepIso F`
is its isomorphism in Mathlib's representation category. Both representations
restrict the same original global section operators; their equivariance is
equality of the underlying sections. All compact sections are included.

`stalkComparison R G X` is the natural isomorphism between the two functors on
equivariant module sheaves. Each functor maps a sheaf morphism by restricting
its actual global component. Thus the comparison commutes with every such
morphism by equality on the original sections. `stalkComparison_inclusion`
proves that the comparison also commutes with both natural inclusions into
global sections.

This is a derived comparison of the imported constructions, with no new claim
from the original literature. It supplies a bridge for consumers of the
existing stalk-based API. It does not generalize Mathlib's stalk universes or
assert an analytic, etale, Godement or derived cohomology comparison.
