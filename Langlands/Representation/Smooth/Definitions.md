# Smoothness, fixed vectors, and admissibility

This module supplies the first representation theory definitions for Task 0.
It makes no assertion of the local Langlands correspondence.

## Mathematical content

Let `R` be a commutative ring, `G` a group, `V` an `R`-module, and
`ρ : Representation R G V` an algebraic representation. For a subgroup `K`,
`Langlands.fixedVectors ρ K` is the submodule

$$V^K=\{v\in V\mid \rho(k)v=v\text{ for every }k\in K\}.$$

The implementation reuses `Representation.invariants` after composing `ρ` with
`K.subtype`; it does not introduce a second representation type or another
construction of invariant submodules.

When `G` has a topology:

- `Langlands.IsSmoothVector ρ v` means that some open subgroup of `G` fixes `v`.
- `Langlands.IsSmooth ρ` requires this property for every vector.
- `Langlands.IsAdmissible ρ` requires smoothness and finite generation over `R`
  of `V^K` for **every open subgroup** `K`.

All four definitions are part of this contribution. `IsAdmissible` is the entry
declaration and uses the preceding definitions. Smoothness is an explicit
conjunct of admissibility, so an arbitrary algebraic representation with finite
fixed spaces is not silently called admissible.

The representation space has no topology. In particular, this definition of
smoothness concerns open fixing subgroups, not differentiability or the usual
topology on a complex vector space. No finite dimension assumption is made on
`V`. Over a field, `Module.Finite` expresses finite dimensionality.

## Source correspondence and scope

The source is Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter II: *Smooth representations*, revision June 16, 2019,
Section 1, page 2, first two paragraphs. They define smoothness by an open
subgroup fixing each vector, introduce `V^K`, and define admissibility by finite
generation of those submodules for each open subgroup.

Citation receipt:

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- Actual source file: `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`
- Locator: Chapter II, Section 1, page 2, first two paragraphs.

This is a deliberate generalization of the domain of those definitions.
Casselman's chapter generally assumes a locally profinite group with additional
countability conditions and a commutative Noetherian coefficient ring containing
the rationals. None of these extra conditions is needed to form these
predicates. This module therefore requires only a commutative ring and a group
with a topology. Continuity of the group operations is not needed to form the
definitions; later theorems must state it when used. No theorem from Casselman
is asserted here at this broader generality.

The quantifier is over all open subgroups, as in this source. An alternative
definition that tests only compact open subgroups is not silently substituted.
Proving their equivalence under suitable local profiniteness and coefficient
hypotheses is future work.

## Dependencies and validation boundary

There are no project mathematical dependencies. The exact prepared environment
is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, with Lean 4.34.0 at commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The imports are `Mathlib.RepresentationTheory.Invariants` and
`Mathlib.Topology.Algebra.OpenSubgroup`. The essential existing interfaces are
`Representation`, `Representation.invariants`, `Subgroup.subtype`,
`OpenSubgroup`, and `Module.Finite`.

The Lean file contains definitions only. Compilation checks elaboration;
independent semantic review is still needed to establish acceptance of the
source translation. No project axioms or proof placeholders are introduced.
