# The corrected-orbit Levi comparison determines the actual centralizers

This internal deduction by Worker 561 supplies the passage from the
whole rational-point Levi comparison in the corrected-orbit modulus target
to an equality on every test scheme.

`dynamicCentralizer_eq_conjugate_of_rationalPoints` concerns two
cocharacters of one split torus in a smooth connected affine group scheme
over any field. Its normalizing point is an actual element of
`normalizerPoints i`. The assumed equivalence tests membership of every
ambient rational point in the first centralizer against membership of
its inverse conjugate in the second centralizer. The conclusion equates
the full first centralizer functor with that of the forward-conjugated
second cocharacter.

The proof uses `groupHom_cocharacterAut_comp` to express the conjugate as
a cocharacter of the same torus. `Dynamic.centralizer_eq_comap_of_iso`
identifies its centralizer with the preimage of the second centralizer
under the inverse inner automorphism. The rational-point map of that
inverse is literal inverse conjugation, by
`rationalPoints_map_innerIso_inv`. Consequently
`dynamicCentralizer_eq_of_rationalPoints_eq` applies. The companion
`dynamicCentralizer_eq_comap_innerIso_inv_of_rationalPoints` presents the
same conclusion as an equality with this preimage.

`standardLevi_eq_comap_innerIso_inv_of_point_comparison` specializes this
result to the exact standard Levi families indexed by finite sets of
actual simple relative roots. `StandardCocharacterStatement` provides
realizing cocharacters for the two root sets, and connected reductivity
provides smoothness and connectedness. The maximal split torus provides
splitness. `normalizerEquiv` uses the displayed
`HasPointNormalizerComparison` to turn each actual point-normalizer lift
into a scheme-normalizing point with the same ambient value. The
conclusion is equality of `standardLevi` subgroup functors with the
inverse-image orientation corresponding to the original pointwise `hK`.

All universes and fields are arbitrary. There is no minimum-length
representative, target simple-root subset, subset containment,
characteristic-zero, perfection, or split-ambient-group condition.
Empty root sets are allowed. These results add no structural premise
to the squared-modulus target and do not prove its Haar identity or
the whole-Levi determinant-character comparison.
