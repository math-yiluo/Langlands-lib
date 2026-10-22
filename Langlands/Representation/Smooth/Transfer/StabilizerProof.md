# Smooth vectors and open stabilizers

This module proves the accepted proposition
`Langlands.SmoothVectorStabilizerStatement`. The reusable lemma
`Langlands.isSmoothVector_iff_isOpen_stabilizer` says that a vector is smooth
exactly when the carrier of its algebraic stabilizer subgroup is open.
`Langlands.smoothVectorStabilizer` supplies the entire accepted target.

The coefficient ring `R`, group `G`, and module `V` have three independent
universe parameters. The ambient assumptions are `CommRing R`, `Group G`,
`TopologicalSpace G`, `AddCommGroup V`, and `Module R V`.
The target itself universally quantifies `IsTopologicalGroup G`, then every
representation `rho : Representation R G V` and every vector `v : V`.
There is no topology on `V`, continuity hypothesis on the representation,
finite generation, finite dimension, local compactness, countability,
Noetherian hypothesis, or coefficient characteristic restriction.
The representation need not be smooth on all its vectors.

The component lemma uses an ambient `IsTopologicalGroup G` instance.
For the closing theorem, `omit [IsTopologicalGroup G]` removes that ambient
parameter, and `intro _ rho v` introduces the instance and variables quantified
inside the accepted proposition. Thus the closing theorem adds no assumption
to its target.

## Implemented proof

In the forward direction, unfold smoothness by introducing an open subgroup
`K` and membership `hK` of `v` in `fixedVectors rho K.toSubgroup`.
By the definition of fixed vectors as invariants of the restricted
representation, `hK` gives `rho g v = v` for each `g` in `K`.
For a group element `g` with membership proof `hg`, the term
`hK ⟨g, hg⟩` proves membership in `rho.stabilizer v`. This establishes
`K.toSubgroup ≤ rho.stabilizer v`. Mathlib's `Subgroup.isOpen_mono`,
applied to this containment and `K.isOpen`, proves that the stabilizer is open.
The topological group instance supplies its separate continuity assumption.

In the reverse direction, package the stabilizer and its assumed openness
as an `OpenSubgroup G`. For each element `g` of this subgroup, `g.property`
is exactly the fixing equation. It therefore proves membership in the
fixed-vector submodule, giving the required witness of `IsSmoothVector`.
The closing theorem introduces the target's quantifiers and applies the
component lemma.

The relevant pinned Mathlib interfaces are
`Representation.stabilizer` and `Representation.mem_stabilizer`
(`RepresentationTheory/Stabilizer.lean`, lines 27-38),
`Representation.invariants` and its membership formula
(`RepresentationTheory/Invariants.lean`, lines 74-81), and
`Subgroup.isOpen_mono`
(`Topology/Algebra/OpenSubgroup.lean`, lines 281-283).

## Provenance and exact dependencies

This is an internal consequence of the open-subgroup definition of smoothness
used in the accepted project definitions. The original convention is in
Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II, revision June 16, 2019, Section 1, page 2, first paragraph.
The original PDF was read with its ambient hypotheses on page 1:

- `literature_id`: `casselman-2019-smooth-representations`.
- SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- File: `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The proof uses the elementary containment argument above at the accepted
generality. It does not apply a Casselman theorem outside that source's
stronger ambient hypotheses or attribute this equivalence to a separately
numbered source theorem.

The exact target is statement artifact
`ef2efb64-ffec-42e3-924e-9d1fa2a680ac`, version 1, published at commit
`6eda9ab3a7272fd3a119b214aefb015331a806d7`, with independent review receipt
`0f5f289e-959f-4cb1-8cd4-b1d72fbc5581` and target fingerprint
`07f5832cb9f1bd548560a0316319aa02b1f4c68ce8582c1f62777e767d778b90`.
Its only project definition dependency is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1, published at commit
`10c81beaaff024987cf2945c64d0c9511f6cb686`, with independent review receipt
`a26076cd-7da3-4621-992f-5c0207f7fe1e`.
Both dependencies were verified accepted, published, and current, and their
local Lean/Markdown hashes matched the retained reviewed pairs.
[StabilizerStatement.md](StabilizerStatement.md) and
[Definitions.md](../Definitions.md) describe them.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at `5ed2965256430c3649e86755f9576b54eca72435`.

Worker 0 authored the proof and initial explanation. Worker 12 reused its
proof terms unchanged, removed the draft label in the module comment,
checked the target and dependencies, and expanded this explanation.
Native compilation of the exact dependencies and this module succeeded.
Declaration inspection confirmed the full three-universe target without an
extra external topological-group instance. Both theorem axiom closures contain
only `propext`, `Classical.choice`, and `Quot.sound`.
These are development checks.
Acceptance requires the registered independent checker, independent semantic
review, and Library publication. This result is a representation-theory
infrastructure theorem and makes no claim to complete local Langlands.
