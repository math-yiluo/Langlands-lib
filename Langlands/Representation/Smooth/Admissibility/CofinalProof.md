# Smoothness and admissibility on a cofinal family

`finite_fixedVectors_of_le` proves the inclusion of fixed-vector submodules
directly: if `H` is contained in `K`, a vector fixed by every element of `K`
is fixed by each element of `H`. Mathlib's `Submodule.inclusion` is injective, so
`Module.Finite.of_injective` transports finite generation from the
larger fixed-vector module over a Noetherian coefficient ring.

For `isSmoothVector_iff_of_cofinal`, choose a family member contained in
the original open fixing subgroup and restrict the fixing equations.
The reverse implication simply forgets family membership.
`isSmooth_iff_of_cofinal` applies this argument vectorwise. These two
smoothness lemmas need no Noetherian hypothesis.

`isAdmissible_iff_of_cofinal` restricts the set of tests in the forward
direction. Conversely, it preserves the assumed smoothness and, for each
open subgroup `K`, chooses a family member `L` contained in `K`.
Finite generation for `L` and `finite_fixedVectors_of_le` then give
finite generation for `K`. `admissibleCofinal` closes the proposition target.

The closing theorem retains the independent universes of the coefficient ring,
group, and representation module. It introduces the Noetherian instance inside
the proposition. Cofinality remains an explicit hypothesis, and
smoothness remains a conjunct on both sides of the admissibility criterion.
Only a topology on the group is required.

[CofinalStatement.md](CofinalStatement.md) records the exact provenance
from Casselman's definition on page 2 and the separate cofinality obligation.

## Dependency and validation status

Its sole project import is
the statement module `Langlands.Representation.Smooth.Admissibility.CofinalStatement`,
published at
`dbf07193b0a67187fcdbad5d5c33e84f862bffab`. The proposition fingerprint is
`a5a3b8c690edd69970b142cde7207b3d41b12ba345f5dc47b2948248ce1548bf`.
Its only project definition dependency is the smoothness and admissibility
definitions of `Langlands.Representation.Smooth.Definitions`, published at
`10c81beaaff024987cf2945c64d0c9511f6cb686`.

The subgroup restriction arguments are proved locally in this module.
This proof therefore does not require a separate antitonicity
proof or any fixed-vector map construction. The finite-generation helper
and the two smoothness criteria are in this same module.

Environment: Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.
