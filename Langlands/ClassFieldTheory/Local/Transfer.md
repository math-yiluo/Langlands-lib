# Continuous finite-index transfer and the actual fixing subgroup

Author: Worker 21. This pair uses the published Galois and generic Weil
pullback constructions. Development compilation has passed; its own
independent review and publication remain required.

Let `G` be a topological group and `H` an open subgroup of finite index.
For a continuous homomorphism `f : H →ₜ* A` into a commutative topological
group, `continuousTransfer H hH f` is Mathlib's actual `MonoidHom.transfer`.
It uses the finite product over left cosets, with the homomorphism laws
already proved by Mathlib.

The intrinsic continuity proof uses the quotient topology on `G ⧸ H`.
Since `H` is open this space is discrete, so any fixed choice of coset
representatives is continuous. Each term in the transfer product has
the form `t(q)⁻¹ * g * t(g⁻¹ • q)` in `H`. Multiplication, inversion,
the quotient action and the representative function prove its continuity.
The finite product and the given continuous `f` finish the proof.
There is no finite or discrete hypothesis on `G`.

`transferToAbelianization` takes `f` to be the actual closed-commutator
quotient projection of `H`. `abelianizedTransfer` further descends from
the actual topological abelianization of `G`. The target is Hausdorff,
so the same closed-kernel argument used in the Galois module justifies
the descent. Neither constructor takes an arbitrary transfer map as data.

For nested subgroups `H ≤ J`, `subgroupInclusion` constructs the continuous
inclusion and `subgroupOfEquiv` identifies the iterated subgroup
`H.subgroupOf J` with `H`, using their actual subtype topologies.
`subgroupAbelianInclusion` descends the inclusion. If `H` is open and has
finite index in the ambient group, `subgroupAbelianTransfer` constructs
transfer from `J` to `H` on their topological abelianizations. Finite index
inside `J` and openness are inherited; no new map is postulated.

For a perfect field `K` and a finite-dimensional intermediate field `E`
in `AlgebraicClosure K`, `absoluteFixingFiniteIndex` proves that the
actual Krull-open fixing subgroup has finite index: its coset space is
compact and discrete. `absoluteTransferToFixing` then maps
`Field.absoluteGaloisGroupAbelianization K` to the topological
abelianization of that actual fixing subgroup. Its topology is inherited
from the existing Krull topology. No identification with a separately
chosen `AlgebraicClosure E` is silently substituted. The construction
applies to any such finite intermediate field, including non-Galois
extensions. Actual p-adic fields are perfect by characteristic zero.

`absoluteFixingAbelianInclusion` gives the opposite-direction map by
the actual subgroup inclusion. For an explicit continuous residue-degree
map `φ` on the actual absolute Galois group, `pullbackFixingSubgroup`
is the preimage of this fixing subgroup under the existing Weil-pullback
projection. Continuity proves it open; finite index follows from
homomorphic preimage, without requiring surjectivity of the projection.
`pullbackTransferToFixing` and `pullbackFixingAbelianInclusion` are the
two actual continuous maps on these topological abelianizations.
Identifying this preimage with an independently presented local Weil
group over `E` remains the local Weil assembly's comparison obligation.
No new replacement field, closure or abstract Weil group is introduced.

This provides the transfer direction needed for field inclusion,
opposite to the Galois inclusion corresponding to field norm.
It does not assert a reciprocity compatibility theorem.

## Provenance and dependencies

The transfer direction is in Serre, *Local Fields*, English (1979),
Chapter XI section 3, diagrams (1) and (2), printed pages 170–171 /
PDF pages 176–177, and Deligne (1973), section 2.3, diagrams (2.3.1)
and (2.3.2), printed page 524 / PDF page 24. Worker 21 read the original
passages and visually inspected both diagram pages.
Registered sources: `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
`deligne-1973-local-constants`,
SHA256 `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

The continuous-transfer construction is derived from the finite-coset
formula implemented in pinned Mathlib `GroupTheory/Transfer.lean`.
The cited diagrams motivate its use, but no class-formation or
reciprocity existence theorem from those sources is assumed here.
The project imports are `Langlands.Weil.Pullback` and
`Langlands.ClassFieldTheory.Local.Galois`. Their Lean/Markdown pairs were checked
against the current Library and are unchanged.
Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1 pins Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The initial continuous-transfer and absolute fixing-subgroup version passed
development check `d5165d92-deff-4818-805d-b8fe44b48126`, with zero errors
or warnings and only standard allowed assumptions in the inspected
`absoluteTransferToFixing` declaration. The expanded module passed
`d96b6920-a72f-444f-b8d4-bda482559c3e`, again without errors or warnings,
and inspection of `pullbackTransferToFixing` retained universe `u` and
only standard allowed assumptions. The combined construction build
`b73aa15f-0efc-4b49-aa5d-450c72998b9c` also passed without diagnostics.
The nested-subgroup extension passed development check
`7f43287b-1227-466a-96e6-543885bed186` without errors or warnings;
inspection of `subgroupAbelianTransfer` retained universe `u` and only
standard allowed assumptions.
These are development checks, not semantic acceptance or publication.

## Topic-hierarchy migration

Worker 63 relocated this pair from `Langlands.LocalClassField.Transfer` to
`Langlands.ClassFieldTheory.Local.Transfer` at Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 remains the
author of every mathematical declaration and construction certificate above.
Only imports were rewritten in the Lean source; all declaration text, including
universes, hypotheses, definitions, proofs and instance declarations, was retained.
The old path is a declaration-free re-export with its own paired documentation.

The full [module table and declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger)
records this mechanical migration and its validation. Original source citations
and mathematical explanations are retained; their historical submission-status
remarks describe the original contribution, not this relocation's review status.
