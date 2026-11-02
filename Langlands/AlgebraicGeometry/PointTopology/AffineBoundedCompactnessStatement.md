# Algebraic boundedness and analytic compactness: statement targets

This module states Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Fact 2.2.3, printed page 70, PDF page 101. The preceding
Definition 2.2.1 and Remark 2.2.2 specify boundedness and the analytic
topology. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered corrections `kaletha-prasad-2024-corrections`, version
1 November 2024, PDF page 24, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
require the field to be Henselian throughout Section 2.2.

The declarations in namespace
`Langlands.AlgebraicGeometry.PointTopology` are:

- `AffineBoundedCompactnessProperty F`: for a nontrivially valued
  rank-one field with its valuation topology, Henselianity of the actual
  valuation ring and local compactness imply the following comparison.
  For every finite-type affine scheme `X` over `F` and every **closed**
  subset `B` of its actual rational points,
  `IsAlgebraicallyBounded F X B ↔ IsCompact B`.
- `LocalFieldAffineBoundedCompactnessProperty F`: the same comparison
  for every nonarchimedean local field, without an additional Henselian,
  discretization, residue-characteristic, or characteristic-zero premise.

These are proposition-valued definitions of targets, not proofs.
The second target is the local-field specialization of the source
comparison, with completeness and Henselianity to be supplied in its
future proof. It is not conditional on the first target having been
proved.

The ambient field assumptions are `[Field F] [ValuativeRel F]
[TopologicalSpace F]`. In the source-level target,
`ValuativeRel.IsNontrivial F` and `ValuativeRel.IsRankLeOne F` express
the nontrivial real-rank-one valuation setting, and
`IsValuativeTopology F` fixes compatibility with the field topology.
The additional premises are explicitly
`HenselianLocalRing (ValuativeRel.valuation F).integer` and
`LocallyCompactSpace F`. The local-field target instead uses precisely
`IsNonarchimedeanLocalField F`; Mathlib derives nontriviality, rank one
and the compatible locally compact topology from that class. Both
mixed and equal characteristic remain included.

Each scheme is an actual object `X` over `Spec F`, with
`IsAffine X.left` and `LocallyOfFiniteType X.hom`. Since the source
scheme is affine, it is quasi-compact, so these hypotheses express the
source's affine finite-type scope. No reducedness or smoothness
hypothesis is imposed.

The carrier is the existing identity-test `RationalPoint F X`, and each
target explicitly installs `rationalPointTopology F X`. That named
topology is transported from the global-section evaluation topology
using the existing rational-point and affine scheme-point equivalences.
It gives the usual analytic topology of the source's affine embedding
description. No arbitrary topology is quantified over. Boundedness is
the imported predicate testing every global regular function; it retains
zero evaluations and requires a nonzero valuation bound for each
function. The compactness assertion retains the source's closedness
premise and makes no claim that every bounded set is compact.

These targets supply the explicit boundedness/topology comparison for
the special compact subgroup program. They do not construct a building,
special vertex, parahoric, or compact subgroup, and do not supply the
general reductive existence target or Renard S19(2), S19(3), or S19(5).
Those remain separate statements on the shared actual KP objects.
