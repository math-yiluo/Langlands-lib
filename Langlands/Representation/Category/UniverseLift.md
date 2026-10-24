# Universe lifts of actual complex representations

This is internal implementation infrastructure, derived from the published
representation definitions and their equivalence-transport laws. It is not
attributed to an original literature theorem.

For a group `G : Type uG`, a complex module `V : Type uV`, and an independent
lift universe `uX`, `Langlands.universeLiftRepresentation` has carrier
`ULift.{uX} V : Type (max uV uX)` and action
`g, up(v) ↦ up(ρ g v)`. Its action laws follow pointwise from those of `ρ`.
The three application lemmas expose the action on an arbitrary lifted vector,
on `up v`, and after `down`.

`Langlands.universeLiftEquiv` uses Mathlib's `ULift.moduleEquiv.symm`.
Its forward map is `up`, its inverse is `down`, and equivariance follows
definitionally from the constructed action. Both maps have application lemmas.
This is an actual `Representation.Equiv` across carrier universes.

The irreducibility equivalence specializes the published
`Langlands.isIrreducible_iff_of_equiv`. With a topology on the group, smoothness
in both directions follows from the published injective and surjective
intertwiner transport lemmas. Admissibility specializes
`Langlands.isAdmissible_iff_of_equiv`, retaining the Library's smoothness and
all-open-subgroups finite-generation convention.

`SmoothRep.universeLift` bundles the lifted action with its proved smoothness.
`SmoothRep.universeLiftEquiv` supplies the corresponding actual representation
equivalence, with forward and inverse application lemmas. The bundled
irreducibility and admissibility equivalences are immediate specializations.
No categorical isomorphism between different fixed-universe categories is
claimed.

The construction needs no topology on the module, no finite dimension,
smallness, resizing, irreducibility, admissibility, or classification hypothesis.
The group, original carrier, and lift universes remain independent.
