# Intrinsic chamber correspondence and reductive local-isogeny graphs

This derived support module removes the base-transport premise from target
simple-root coverage and the resulting local-isogeny graph certificates. It
works over every field in every universe on the actual character and
cocharacter lattices of the supplied split maximal tori. The finite reduced
root data and all characteristic-power factors are retained.

For a generic source chamber, the published root-pairing formula proves that
its actual coweight pushforward is generic on the target. An integral base is
chosen separately for each regular coweight using
`RootDatumCoweightFace.exists_base_support`. Positivity on each base's support
identifies its positive system with the corresponding chamber. The reflection
criterion in `RootDatumIsogeny.mem_support_iff_of_coweight_signs` identifies the
two base supports. Positive indecomposability then identifies their images with
the intrinsic simple relative roots. This proves
`simple_root_coweightMap_iff_of_chambers` without a base-transport hypothesis.

For a supplied `SimpleIsogenyGraph`, every target simple root therefore comes
from a source simple root. The graph's associated source direction annihilates
that root, and the actual transpose pairing equation makes its pushed target
direction annihilate the target root. This is `target_coverage`. The already
published target projection criterion yields `second_geometry`, with flatness,
surjectivity, local finite presentation and quasi-compactness. Combining it
with the source projection geometry gives `faithfullyFlatGraph`, and the
published graph reductivity construction yields `reductiveGraph`.

These constructors preserve the supplied graph and both actual projections.
The connected reductivity, split-torus, maximal-torus, torus-isogeny and actual
weight-map compatibility inputs in their types remain explicit. This module
provides neither first-projection invertibility nor final ambient isogeny
realization or fixed-torus extension. It is an internal deduction from the
imported root-datum, chamber, and local-isogeny graph interfaces.
