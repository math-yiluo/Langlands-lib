# Comparing frame constructions across bases of opens

This is derived internal infrastructure for actual projective bundles.
For an actual module sheaf `M` of rank `n + 1`, `FrameAtlas` specifies a
topological basis of opens and a genuine module-sheaf frame on each basis
member. It does not contain a projective scheme, gluing comparison, or
universal family.
`ofLocallyFree` constructs such an atlas from the fixed-rank
local-freeness predicate itself, using all frame-bearing opens.

The basis gives a small thin locally directed cover by its actual open
subschemes. `cocycle` constructs the strict dual-frame coordinate cocycle
on this cover. Its identity and composition laws follow from restriction
and composition of actual frame changes, with coefficients transported
through the canonical comparison between sections on an open and global
sections of its open subscheme. `bundle` is the resulting actual glued
scheme, with structure morphism `toBase`.

Assume `M` is locally free of the specified rank. Each basis member belongs
to the fixed cover of all frame-bearing opens. `comparisonCoordinate`
uses the change from the atlas's genuine dual frame to the fixed genuine
dual frame on that same open. Their cancellation and restriction
identities prove the required transition compatibility.
`comparisonChart` applies this invertible coordinate action before the
fixed frame-bundle chart. The charts are compatible and Cartesian, since
the coordinate action is an isomorphism over the chart's base.

These constructed charts supply a `CartesianAtlas` on the fixed
`frameBundle`. The previously constructed Cartesian-atlas comparison
therefore gives `toFrameBundleIso`, an actual scheme isomorphism with the
specified chart formulas that commutes with the structure morphisms.
Composing through this fixed bundle yields `comparisonIso` between the
actual projective schemes constructed from any two frame bases. These
comparisons are the identity for the same atlas and compose transitively.

All constructions are derived from genuine sheaf frames and the earlier
coordinate-gluing and Cartesian-atlas constructions; no new external
source assertion is invoked. The basis requirement supplies locally
directed cover indices; this file does not claim a construction from an
arbitrary cover without passing to such a basis. Tensor-line invariance,
the tautological invertible sheaf, the invertible-quotient universal
property, and ordinary polarized moduli representability remain further
obligations.
