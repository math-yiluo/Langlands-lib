# All-test homogeneous coordinates for actual linear torus actions

This is an internal construction from the published natural finite Lie
coordinates and the actual vector-action comparison. It introduces no new
geometric hypothesis or literature assertion. Work is over an arbitrary field
`k : Type u`, with an affine target group scheme `V` and its original action
`b : AutomorphicAction S.toGrp V`.

`IsLinearVectorCoordinates.homogeneous_action` extends the diagonal formula of
`VectorHomogeneousCoordinates` from affine tests to every scheme over `Spec k`.
Its inputs are natural vector coordinates satisfying the existing all-test
scalar-linearity condition, an affine acting commutative group `S`, and a supplied
`HomogeneousLieBasis b (𝟙 S.toGrp)`. For each basis index, the coefficient of the
original action equals the coefficient of the original point multiplied by the
value of that index's actual character. The character value is the unit obtained
from the actual character morphism through `Gm.pointsEquiv`.

The implemented proof first transfers the affine coefficient formula across
`Scheme.ΓSpecIso`, using its injectivity and multiplicativity. The product
`S.X ⊗ V.X` is affine. An affine presentation of that product tests the formula
at its two universal projection points. Naturality of the coordinates and of the
original action, and injectivity of pullback along the presentation isomorphism,
give the formula on the universal product. Pulling this identity back along
`lift s x` proves it on an arbitrary test scheme. Naturality of
`Gm.pointsEquiv` identifies the pulled-back coefficient with the original
character evaluated at `s`.

`HomogeneousVectorCoordinates b` packages a finite dimension, natural all-test
multiplicative coordinate equivalences, actual character labels, and this
diagonal equation for the original action. It does not replace the original
action by an unrelated representation. The construction
`IsLinearVectorCoordinates.homogeneousCoordinates` produces this package for
any split torus: it uses the existing finite homogeneous basis of the actual Lie
kernel, changes coordinates to that basis, and applies the preceding theorem.
Affineness of the acting torus follows from the supplied splitting.

The field characteristic and universe are arbitrary. The labels may repeat or
be zero, and dimension zero is permitted. This unit proves diagonalization of
the supplied linear vector action. Identification of the original semigroup
subgroups with coordinate blocks, the central-unipotent induction, and the full
`SemigroupOrderedProductStatement` remain separate obligations.
