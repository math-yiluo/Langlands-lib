# Proof of smoothness and continuity of discrete orbit maps

`Langlands.smoothDiscreteOrbit` proves exactly
`Langlands.SmoothDiscreteOrbitStatement` from
[DiscreteOrbitStatement.lean](DiscreteOrbitStatement.lean).
It preserves the independent coefficient-ring, group and module universes
`uR`, `uG` and `uV`. The coefficient ring is any commutative ring, and the
representation is the existing algebraic `Representation R G V`.
The group has its supplied topology. The topological-group instance is
quantified inside the target, and the target installs the discrete topology
`TopologicalSpace V := ⊥` internally. The closing theorem has no external
module-topology or topological-group parameter.

The theorem proves both the equivalence for each vector and the equivalence
between `Langlands.IsSmooth ρ` and continuity of every orbit map. It requires
no finite dimension, admissibility, nonzero assumption, local compactness,
separation, total disconnectedness or coefficient characteristic restriction.

## Implemented proof

The reusable theorem
`Langlands.isSmoothVector_iff_continuous_orbitMap` works with any explicitly
discrete topology on `V`. It first applies the published
`Langlands.isSmoothVector_iff_isOpen_stabilizer` from
[Transfer/StabilizerProof.lean](Transfer/StabilizerProof.lean), replacing
smoothness of `v` by openness of the algebraic stabilizer `ρ.stabilizer v`.

Suppose that stabilizer is open. For each `g : G`, the fibre of the orbit map
above `ρ g v` equals

`{x : G | g⁻¹ * x ∈ ρ.stabilizer v}`.

The representation multiplication law rewrites membership on the right as
`ρ g⁻¹ (ρ x v) = v`. Mathlib's `Representation.inv_apply_eq_iff` identifies
this equation with `ρ x v = ρ g v`, proving the displayed fibre equality.
The map `x ↦ g⁻¹ * x` is continuous in the topological group. Thus this fibre
is open as the inverse image of the open stabilizer.
`IsLocallyConstant.iff_isOpen_fiber_apply` gives local constancy of the
orbit map, and `IsLocallyConstant.continuous` gives continuity.

Conversely, if the orbit map is continuous, its inverse image of the open
singleton `{v}` is open because the module is discrete. This inverse image
is definitionally the carrier of `ρ.stabilizer v`. The same published
stabilizer equivalence recovers smoothness of the vector.

The closing theorem introduces the target's topological-group instance and
representation, installs exactly its discrete module topology, and applies
the vectorwise result. Since `IsSmooth ρ` means that every vector is smooth,
the second conjunct follows by applying the two directions separately to
each vector. The target and its imported files are unchanged.

## Original source and scope

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.1.1, definition and following unnumbered
remark, printed page 58 / PDF page 64. The remark uses the discrete topology
on the representation space and proves the global equivalence using open
inverse images. III.1.3, printed page 59 / PDF page 65, also explicitly calls
the orbit maps of smooth representations locally constant. These passages
were read directly, and the main III.1.1 passage was visually checked.

- Registered source: `renard-2026-representations-groupes-reductifs-padiques`.
- SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Original PDF: `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

Renard states the result for complex representations of t.d. groups. His
II.1.1 convention, printed page 30 / PDF page 36, includes Hausdorffness and
a basis of compact open neighborhoods. The arbitrary-ring, arbitrary-topological-
group statement and its explicit vectorwise clause are derived generalizations,
as documented in the unchanged statement companion. The implemented proof
uses only open stabilizers, translation continuity and the algebraic
representation laws, so none of the source's additional ambient hypotheses
is needed. It does not prove the Hecke-module equivalence or other Chapter III
assertions.

The project dependencies are the published target and stabilizer proof, with
their existing definitions of fixed vectors and smoothness. The extra Mathlib
import is `Mathlib.Topology.LocallyConstant.Basic`; the representation and
topological-group facts come from the project imports. The pinned environment
is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 55 authored this proof and explanation. Reused published results are
imported by their Lean names. Acceptance and publication require the separate
machine checks and independent semantic review.
