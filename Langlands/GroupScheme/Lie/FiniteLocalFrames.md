# Finite local frames of a smooth group scheme's actual Lie sheaf

For an arbitrary scheme `S : Scheme.{u}` and group scheme `G` over `S`,
this module assumes only `hG : Smooth G.X.hom`. It proves finite local
freeness of the actual cotangent sheaf at the identity and the actual
internal Lie sheaf defined in `Langlands.AbelianScheme.Lie`.

`cotangentAtIdentity_hasFiniteLocalBasis` applies the published finite
local basis theorem for smooth relative differentials and then pulls
that witness back along `G.identitySection`. The result concerns exactly
`G.cotangentAtIdentity`, which is this pullback of relative differentials.
`lie_hasFiniteLocalBasis` applies the published finite local basis
theorem for the internal sheaf dual. Its target is exactly `G.Lie`,
defined as the dual of that cotangent sheaf.

`cotangentFiniteLocalBasisData` chooses a local generator witness from
the proved cotangent existence result. Its instances certify that the
generator maps are isomorphisms and their index types are finite.
`cotangentFiniteLocalBasisTrivialization` is the isomorphism from the
free module sheaf on those indices to the actual cotangent sheaf over
each chosen open.

`lieFiniteLocalBasisData` dualizes these cotangent frames using
`dualLocalGeneratorsData`. Thus the Lie frames use the same open cover
and the same basis index types as the cotangent frames. The cover
indices and these equalities are inherited definitionally from that
published construction. The module supplies local freeness, finite
type and `Fintype` instances, and `lieFiniteLocalBasisTrivialization`
gives an actual isomorphism from the corresponding finite free sheaf
to the actual Lie sheaf on each open.

This is an internal composition of published differential, pullback
and internal duality results. It generalizes the finite local basis
argument for abelian schemes in `Langlands.AbelianScheme.LieDeterminant`
to any smooth group scheme, and chooses the Lie frames by dualizing
the chosen cotangent frames. No new literature translation is claimed.
There is no affine base or affine group hypothesis, no global free
basis, and no prescribed constant rank. The basis cardinalities may
vary between cover members. The choices assert no compatibility with
group homomorphisms or base change.
