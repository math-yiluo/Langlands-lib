# Character twists of invariant submodules and quotients

For a commutative ring `R`, a group `G`, an `R`-module `V`, an algebraic
representation `rho`, and a homomorphism `chi : G →* Rˣ`, this module
constructs the correspondence between the subrepresentations of `rho`
and those of `twist chi rho`.

`twistSubrepresentation chi S` retains exactly the underlying submodule
of `S`. Stability follows because the twisted action is
`chi(g) • rho(g)` and a submodule is closed under scalar multiplication.
`untwistSubrepresentation` retains the same submodule and proves stability
by multiplying the twisted action by the inverse unit `chi(g)⁻¹`.
Neither map changes vectors, scalar multiplication, or inclusions.

`twistSubrepresentationOrderIso` bundles these maps, their inverse laws,
and preservation and reflection of the order. It uses the existing
`Subrepresentation` lattice. The inverse laws follow by equality of
the underlying submodules; the order comparison is definitionally the
same inclusion. The bundled order equivalence can be used with Mathlib's
order API without introducing a second notion of invariant subspace.

The two further representation equivalences use identity linear maps:

- `twistSubrepresentationEquiv` identifies the twist of the representation
  restricted to `S` with the representation restricted to the corresponding
  twisted subrepresentation.
- `twistQuotientEquiv` identifies the twist of the quotient by `S` with the
  quotient of the twisted representation by the corresponding subrepresentation.
  The quotient modules are definitionally the same. The intertwining
  obligation is checked on quotient representatives.

All inverse, stability, linearity and intertwining fields are proved in
the constructions. These are intrinsic well-definedness obligations.
There is no assumed theorem of exactness or classification hidden in a field.
The coefficient, group and module universes are independent. There are no
topology, continuity, smoothness, admissibility, Noetherian, dimension or
irreducibility hypotheses. In particular, no new definition of irreducibility
or finite length is introduced here.

## Provenance and dependencies

These are internal algebraic constructions from the accepted scalar-twist
formula. They are not attributed as additional theorems from the motivating
local Langlands literature. The only project dependency is
`Langlands.Representation.Twist.Definitions`, artifact
`c83db975-8b79-4fbb-9901-2db836910a0a` version 1, published at
`3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
Before development its exact Lean and Markdown hashes were compared with
the current published bundle; both matched, with no unavailable dependencies.

The pinned Mathlib interfaces inspected are:

- `Mathlib.RepresentationTheory.Subrepresentation`: the `Subrepresentation`
  structure, `toRepresentation`, its order/lattice, and
  `toSubmodule_injective`.
- `Mathlib.RepresentationTheory.Basic`: `Representation.quotient`, defined
  by the induced linear endomorphism on the submodule quotient.
- `Mathlib.RepresentationTheory.Intertwining`: `Representation.Equiv`,
  retaining the established intertwiner convention.

No parallel representation, subrepresentation, or quotient type is created.
The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`
version 1: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 4 authored this construction pair. Compilation is a development
check; mathematical acceptance requires independent review and publication.
