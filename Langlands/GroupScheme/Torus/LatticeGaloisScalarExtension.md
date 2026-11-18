# Character transport after changing the ground scheme

Worker 509. This is derived compatibility of the existing descent-point,
character-transport and canonical direct/iterated base-change constructions.
It makes no new structural assumption. The first three comparisons apply over
arbitrary schemes; the last two apply to compatible towers of fields at every
universe parameter.

This unit imports `SimplyConnected.AlmostSimpleFactorDescent` and reuses its
published `descentPoint_left_fst` lemma, which states that descent transport
preserves the projection to the original group scheme. It adds no duplicate
declaration for that existing helper.
`descentPoint_scalarExtension_inv` compares descent over the original ground
scheme with descent after changing that scheme. The upper endomorphism fixes
the map to the extended ground scheme. The canonical inverse tower
isomorphism intertwines the two descent operations. Projection to the original
group, the tower-isomorphism projection identity, and the first lemma prove
the comparison.

`characterLattice.transport_scalarExtension` transports this point identity to
characters. Equality on every test-scheme point proves equality of characters.
The proof evaluates both transported characters using `transport_points`,
then uses the descent-point comparison. The equality-of-base-maps version
`transport_scalarExtensionOf` is the same assertion after changing the
composite base map along its specified equality.

For a tower `k → E → L`, the comparison
`galoisRepresentation_scalarExtension` identifies the original character
Galois action of an `E`-automorphism of `L`, regarded as a `k`-automorphism,
with the action after ground-field extension to `E`. The same upper field and
the canonical direct/iterated torus comparison are used. The explicit equality
of spectral base maps is the equality induced by the scalar-tower law.
No finite-dimensional, separable, or Galois hypothesis is needed here.

`scalarExtensionGaloisEquiv` packages this as an equivalence of integral
representations of `Aut_E(L)`: restrict the original `Aut_k(L)` representation
along `AlgEquiv.restrictScalarsHom k`, and compare it with the representation
of the base-changed torus. Its linear equivalence is the integral character
lattice equivalence induced by the canonical tower isomorphism; the preceding
pointwise theorem proves its intertwining law.

Provenance is internal derived interface material. This unit proves no
root-factor realization or based star-action comparison, and uses no local
rank-one classification or Kneser–Tits theorem.
