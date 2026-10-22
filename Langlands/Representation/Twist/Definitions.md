# Character twists on the existing representation interface

For a commutative ring `R`, a group `G`, an `R`-module `V`, a representation
`rho : Representation R G V`, and a unit-valued homomorphism
`chi : G →* Rˣ`, `Langlands.twist chi rho` is the representation on the same
module with action

`(twist chi rho)(g)(v) = chi(g) • rho(g)(v)`.

`characterRepresentation chi` specializes this to the trivial action on `R`.
It is a free rank-one scalar representation; the name does not assert that
the coefficient ring is a field. `twistIntertwining` and `untwistIntertwining`
keep the underlying linear map and respectively introduce or cancel a common
twist. Their inverse relationship is bundled as `twistIntertwiningEquiv`, an
`R`-linear equivalence of intertwiner spaces. `twistEquiv` transports a
representation equivalence while retaining its underlying linear equivalence.

## Provenance and scope

The convention is the scalar realization of tensoring with a one-dimensional
representation, used in Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Invent. Math. 139 (2000),
439-455, Section 1.2(2), printed page 440 (PDF page 2).
The formulas in that source twist the Weil representation by `chi ∘ tau_F`
and the general linear group representation by `chi ∘ det`. This module
provides the general algebraic operation needed by both formulas. It does
not construct reciprocity, the determinant character, or the correspondence.

- Literature ID: `henniart-2000-simple-proof`.
- Exact source SHA-256:
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Retained original:
  `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
- Additional locator: Section 1.1, footnote 1, printed page 439 (PDF page 1).

Henniart reserves "character" for a unitary continuous homomorphism to complex
units and uses "quasicharacter" for a general continuous one. In these Lean
names, a character means only a unit-valued algebraic homomorphism. No
continuity, unitarity, topology, finite dimensionality, or irreducibility is
assumed. Extension from complex vector spaces to modules over arbitrary
commutative rings is a project generalization, justified by the displayed
scalar-action formula, rather than a theorem quoted from Henniart.

The intertwiner constructions are internal algebraic consequences of this
definition. Linearity commutes with multiplication by `chi(g)`, and multiplication
by its inverse cancels the scalar. These are construction obligations, not
unproved mathematical assumptions.

## Exact dependencies

There are no project dependencies. The module imports
`Mathlib.RepresentationTheory.Intertwining`, using its existing `Representation`,
`Representation.IntertwiningMap`, and `Representation.Equiv` interfaces.
The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Worker 4 searched the pinned `Mathlib/RepresentationTheory` sources for twist
constructors and inspected `Basic.lean` and `Intertwining.lean`. No matching
scalar twist constructor was found. This module reuses their representation
and morphism types instead of adding parallel types.

Compilation is an elaboration check. Independent review is required for
mathematical acceptance and publication.
