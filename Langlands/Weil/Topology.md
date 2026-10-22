# The topology determined by open inertia

`Langlands.Weil.TopologyProperties` is a proposition definition for a future
proof. For every topological group `Γ` and continuous homomorphism
`φ : Γ → ProfiniteIntegers`, it asserts that:

1. The existing product-subtype topology on `Pullback φ` makes it a
   topological group.
2. `inertiaInclusion : ker φ → Pullback φ` is an open embedding. Its domain
   has exactly the subgroup topology inherited from `Γ`. Thus this single
   condition specifies both openness of its image and the given topology
   on inertia.
3. The subgroup `inertiaSubgroup φ`, defined as the kernel of degree, is open.
4. Any topology `t` on the **same underlying pullback group**, making that
   group a topological group and the same inertia inclusion an open
   embedding from the fixed original inertia topology, equals the existing
   product-subtype topology.

Before introducing the arbitrary topology `t`, Lean captures the original
pullback topology as `originalTopology` and the original inertia topology as
`originalInertiaTopology`. Item 4 explicitly uses these fixed values: the
embedding has source topology `originalInertiaTopology` and target topology
`t`, and the conclusion is `t = originalTopology`. No topology is synthesized
on the right of this equality within the scope of `t`. The topology on `Γ`
and the discrete integers is unchanged. There are no Hausdorffness,
compactness, or surjectivity hypotheses.

The intended uniqueness argument is that group translations are
homeomorphisms and the open inertia cosets cover the group. Consequently
the topology on inertia determines the topology on every coset and on their
union. Openness of the degree kernel follows from discreteness of the
integer coordinate. The topology on its image under inertia inclusion is
the original one because the embedding is `g ↦ (g,0)`.
This is a mathematical explanation of the proposed target; no proof of this
target is implemented in this statement module.

## Original source and scope

Guy Henniart, *Representations du groupe de Weil d'un corps local*,
L'Enseignement Mathematique (2) 26 (1980), Section 2.1, printed page 158
(PDF page 5), specifies that inertia is open in the local Weil group and
has the topology induced from the absolute Galois group. The statement above
expresses those requirements for the generic pullback and states their
uniqueness in the category of group topologies on that fixed group.

- `literature_id`: `henniart-1980-weil-representations`
- `content_sha256`: `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`
- File: `C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`
- Locator: Section 2.1, printed page 158, PDF page 5, inertia topology.
- [Original source DOI](https://doi.org/10.5169/seals-51064).

This generic uniqueness statement is derived content, not a theorem quoted
from Henniart. The actual Weil-group identification still requires the
absolute-Galois and residue-field results enumerated in `Pullback.md`.
In particular, continuity of projection does not identify the Weil topology
with the subgroup topology inherited from the original Galois group.

## Dependencies and validation

The only project definition dependency is the exact version of
`Langlands.Weil.Pullback` in the submission manifest. The algebraic
image/kernel statement is a separate target and is not used as a proved
dependency in this definition of a proposition. No project theorem is imported.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.

The manifest records the checked proposition fingerprint. Compilation verifies
the statement's elaboration, not its truth. Independent statement acceptance
and publication must precede submission of a proof at an exact target version.
