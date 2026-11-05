# Compactness of finite extensions of anisotropic tori

Authors: Worker 1232 and Worker 1567.

`AnisotropicTorusFiniteQuotientCompactnessStatement.{u}` asserts that an
actual affine group scheme `G` over a nonarchimedean local field has compact
rational points whenever `HasAnisotropicTorusFiniteQuotient G` holds. Its
topology is exactly `rationalPointTopology F G.X`. Both the statement and
`anisotropicTorusFiniteQuotientCompactness`, its proof, allow arbitrary
universe `u` and either field characteristic.

The algebraic hypothesis supplies an actual closed anisotropic torus
`j : T → G` and an actual finite group scheme `Q` with an fppf quotient
`q : G → Q` by the full all-test range of `j`. No smoothness, connectedness,
or reducedness is required of `G` or `Q`. Local finite type of `G` follows
from the fppf quotient's local finite presentation and the finite structure
map of `Q`.

`HasAnisotropicTorusFiniteQuotient.isCompact_univ` implements the proof.
The published connected-reductivity theorem for tori supplies affineness
and smoothness of `T`, hence its local finite type. The published
`IsTorus.isCommMonObj` equips this same group object with the commutative
group-scheme presentation needed by
`IsAnisotropic.isCompact_univ_of_isTorus`. That theorem proves compactness
of the canonical points of `T` using torus norm-kernel compactness.
The underlying group scheme and its rational-point topology are unchanged
by this commutative presentation.

The existing
`compactSpace_rationalPoints_of_finite_fppf_quotient` then makes `G(F)`
compact. Its argument uses the compact image of `T(F)` as the point
kernel and covers `G(F)` by finitely many translates indexed by attained
points in `Q(F)`. It requires no surjectivity of `G(F) → Q(F)` and retains
possible nonreduced finite quotient data.

This is a derived composition of the published torus geometry,
anisotropic-torus compactness, and finite-quotient compactness APIs. The
implementation adapts the earlier conditional `compactSpace` proof in
`AnisotropicTorusFiniteQuotient`, replacing its use of the general
`AnisotropicCompactnessStatement` with the proved torus theorem.
No general reductive anisotropic compactness proposition is assumed.
The full-center application still needs its algebraic quotient,
multiplicative-type structure, and maximal-split quotient anisotropy.
This result alone does not prove the full-center quotient target.
