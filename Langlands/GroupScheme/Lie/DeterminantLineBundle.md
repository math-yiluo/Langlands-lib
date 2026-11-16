# Determinant line of a smooth group scheme's actual Lie sheaf

For every scheme `S : Scheme.{u}` and smooth group scheme `G` over `S`,
`smoothLieDeterminant G hG` is the actual line bundle obtained by applying
`finiteLocallyFreeDeterminant` to the proved finite local basis condition on
`G.Lie`. The module sheaf is the internal dual of the cotangent sheaf at the
actual identity section. Its rank may vary on the base.

`smoothLieDeterminantIso` takes the Lie differential of an actual group-scheme
isomorphism and then its determinant. The identity and composition lemmas follow
from the corresponding laws of the Lie functor and of the determinant maps.
These comparisons concern arbitrary smooth group schemes and require no
commutativity, affineness, connectedness or properness.

`smoothLieDeterminantBaseChangeIso` compares the pullback of this determinant
line along any base morphism with the determinant of the actual base-changed
Lie sheaf. Smoothness of that group is proved from stability of smoothness under
pullback. The comparison composes the chosen finite locally free determinant
pullback isomorphism with the determinant of `smoothLieBaseChangeIso`.
The naturality lemma identifies the two resulting determinant isomorphisms for
every actual group-scheme isomorphism. Its proof upgrades the Lie base-change
naturality square to an equality of module isomorphisms, then uses determinant
pullback naturality and composition of determinant maps.

This is internal derived content combining the established smooth-group Lie
frames and Lie base-change comparison with the actual finite locally free
determinant construction. It supplies neither base-morphism identity and
composition laws nor ampleness or parabolic representability.
