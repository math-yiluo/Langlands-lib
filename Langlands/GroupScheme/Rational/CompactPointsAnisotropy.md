# Compact canonical rational points force anisotropy

Author: Worker 1563.

`compactPointsAnisotropy_proof` proves exactly
`Langlands.GroupScheme.CompactPointsAnisotropyStatement.{u}`. It implements
the compactness-to-anisotropy implication for any
actual affine group scheme over a nonarchimedean local field. It uses the
canonical identity-test rational-point topology throughout.

A compact unit group would have a valuative bound on its scalar values by
the published compact-scalar bound. Multiplying that nonzero bound by an
element of valuation greater than one contradicts the bound. Thus the
entire field unit group is not compact.

The published split-torus affine-point homeomorphism, composed with the
published rational-to-affine point homeomorphism, identifies the split
torus points with a product of field unit groups. If the index type has an
element, projection is a continuous surjection to the unit group.
Consequently a compact split torus must have empty index type.

Finally, a closed split subtorus induces a closed embedding on canonical
rational points. Pulling back compactness of the whole ambient point set
gives compactness of the split torus. The published `isAnisotropic_iff`
then proves split-rank-zero anisotropy.

This is the first implication of Kaletha--Prasad, Theorem 2.2.9, printed
pp.71--73 / PDF pp.102--104, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 1 November 2024 corrections are registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`;
PDF pp.24--25 contain the section 2.2 qualifications. The direct
implementation uses the already published canonical point comparisons
and valuation lemmas, and needs only affineness of the ambient group.
The stronger affine scope is derived from this argument. It does not
assert the reverse implication.

All results are uniform in universe `u`. Finite split-torus index types
may be empty; the proof uses a coordinate only after assuming an element
of the index type. No characteristic, splitting, representation,
boundedness, or connected reductivity premise is introduced.
