# Smoothness and continuity of discrete orbit maps

`Langlands.SmoothDiscreteOrbitStatement` states the continuity characterization
in Renard III.1.1, including its vectorwise form. It uses the existing
`Representation R G V`, `Langlands.IsSmoothVector`, and `Langlands.IsSmooth`;
it introduces no representation type or alternative smoothness predicate.

For a representation `ρ` of a topological group `G` on an `R`-module `V`, give
`V` the discrete topology. The two conjuncts assert:

1. For every `v : V`, some open subgroup fixes `v` if and only if its orbit map
   `g ↦ ρ g v` is continuous.
2. The representation is smooth if and only if every such orbit map is
   continuous.

The topology on `G` is the supplied topology. The proposition itself installs
`TopologicalSpace V := ⊥`, the discrete topology, before forming either
continuity assertion. It takes no ambient topology on `V`. In particular, it
does not refer to the usual topology on a complex vector space or assert
continuity into an arbitrary topology.

## Source and generality

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.1.1, the definition and immediately
following unnumbered remark, printed page 58 / PDF page 64. The remark
characterizes smoothness by continuity of all orbit maps when the complex
representation space is given the discrete topology. III.1.3, printed page 59 /
PDF page 65, also describes the orbit maps of a smooth representation as locally
constant.

- Registered source: `renard-2026-representations-groupes-reductifs-padiques`.
- SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Original PDF:
  `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
- Ambient t.d. convention: II.1.1, printed page 30 / PDF page 36.

Renard works here with complex representations of a t.d. group; his t.d.
convention requires Hausdorffness and a basis of compact open neighborhoods.
This statement deliberately generalizes that setting to a commutative ring
`R`, an `R`-module `V`, and any topological group `G`. The vectorwise clause is
an explicit refinement of the source's global formulation. Neither compactness
nor linear algebra over the complex numbers is needed for this characterization:
continuity makes the stabilizer the open inverse image of the singleton `{v}`,
and an open stabilizer makes each nonempty orbit fibre an open coset.
The global equivalence then quantifies the vectorwise equivalence over `v`.
These observations explain the generalization; this file does not implement
their proof.

The ring, group, and module have independent universe parameters `uR`, `uG`,
and `uV`. `IsTopologicalGroup G` is universally quantified inside the proposition
value, retaining the group-operation continuity hypothesis in the exact target.
No local compactness, total disconnectedness, countability, finite dimension,
finite generation, admissibility, smoothness premise, or coefficient
characteristic restriction is imposed.

## Dependencies and status

The project import is
[Definitions.lean](Definitions.lean), documented in
[Definitions.md](Definitions.md). It supplies the existing open-subgroup
definition of smoothness.
The published theorem
`Langlands.isSmoothVector_iff_isOpen_stabilizer` in
`Langlands.Representation.Smooth.Transfer.StabilizerProof` is a reusable route
for a separate proof. The current file neither imports that proof nor repeats
its implementation.

This is a proposition definition only. Independent semantic review and
publication of the statement, followed by a separate exact-target proof, remain
required. It does not cover the Hecke-module equivalence, the representation
category's abelian properties, or the rest of Chapter III.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0
at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.
Worker 6 authored this statement and explanation.
