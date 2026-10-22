# Compact open subgroups in the actual p-adic matrix groups

Author: Worker 6.

For every algebraic `PadicField p` and every supplied `TopologicalData`, this
module constructs nonarchimedean certificates and choices of compact open
subgroups inside arbitrary identity neighborhoods of the following actual
groups: GL, the ordered upper and opposite block parabolics, their two
unipotent radicals, the product Levi, and the full upper unipotent group.
The canonical abbreviations use `canonicalTopologicalData`, so they need no
additional realization premise. All topologies are precisely those supplied
by the corresponding `Padic`, `PadicBlocks`, `PadicOppositeBlocks`, and
`PadicUpperUnipotent` modules.

The GL certificate specializes the intrinsic valuative theorem from
`Nonarchimedean`. A private pullback lemma proves that a group with a topology
induced by a homomorphism into a nonarchimedean group is nonarchimedean:
write an identity neighborhood as containing a preimage neighborhood,
choose an open subgroup in the latter, and take its continuous inverse image.
Subgroup inclusions give the parabolic and unipotent certificates. For the
Levi product, the proof first applies the subgroup argument to its actual
block-diagonal image, then pulls back along the proved continuous
multiplicative equivalence `leviEquivContinuous`. No topology or matrix
decomposition property is assumed through a new wrapper.

The chosen compact open subgroups come from the accepted general theorem
`Langlands.compactOpenSubgroupBasis`. All its hypotheses are discharged:
nonarchimedeanness is proved as above, and local compactness is supplied by
the companion p-adic topology constructions, including their intrinsic
closedness proofs. Classical choice selects the subgroup, and its compactness
and containment proofs are retained in the returned subtype. The underlying
object is Mathlib's `OpenSubgroup`. Openness is therefore part of the actual
subgroup construction, not an unproved proposition.

This also supplies a compact open subgroup inside any open subgroup: give its
underlying set and `OpenSubgroup.mem_nhds_one` to the corresponding construction.
All natural ranks are allowed; block shapes have the positivity and sum
conditions from `BlockShape`. No separation or local compactness assumption
is added to the caller's algebraic p-adic field.

This module is a derived construction from the following project results:
`Langlands.Group.GL.Nonarchimedean` proves the intrinsic theorem
`Langlands.valuativeGeneralLinearNonarchimedean`, whose proposition is defined
in `Langlands.Group.GL.NonarchimedeanStatement`.
`Langlands.Topology.CompactOpen.NeighborhoodBasis` proves
`Langlands.compactOpenSubgroupBasis` from nonarchimedeanness and weak local
compactness. The actual matrix groups, their supplied p-adic topologies and
local compactness certificates are provided by `Langlands.Group.GL.Padic`,
`Langlands.Group.GL.PadicBlocks`, `Langlands.Group.GL.PadicOppositeBlocks`,
and `Langlands.Group.GL.PadicUpperUnipotent`. The generic block and radical
constructions and their proofs are documented in `Langlands.Group.GL.Blocks`,
`Langlands.Group.GL.OppositeBlocks`, and `Langlands.Group.GL.UpperUnipotent`.
These modules are imported by their Lean names; their paired Markdown describes
the source conventions and implemented proofs.
