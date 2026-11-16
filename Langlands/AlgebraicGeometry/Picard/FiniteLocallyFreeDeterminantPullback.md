# Coherent pullback of finite locally free determinants

This derived module constructs pullback comparisons for the actual determinant
line of any module sheaf with a finite local basis, on an arbitrary scheme in
universe `u`. The rank may vary between local charts.

`finiteLocallyFreeDeterminantPullbackIso hM f` first uses the determinant
comparison for the pullback of the chosen frames, then changes those pulled-back
frames to the frames chosen from the proved finite local basis condition on the
target scheme. It is an isomorphism from the actual pullback of the determinant
line to the chosen determinant line of the actual pulled-back module sheaf.

The naturality theorem intertwines this comparison with the determinant of
every actual module-sheaf isomorphism. The identity theorem composes it with the
determinant of the canonical module identity-pullback comparison and obtains the
canonical identity-pullback isomorphism of line bundles. The composition theorem
similarly compares two successive pullbacks with pullback along the composite
scheme morphism, using the canonical comparison isomorphisms for module sheaves
and line bundles.

The proofs reuse the variable-rank determinant frame coherence and naturality
theorems. Naturality of frame changes moves the intermediate chosen frames
through pullback, and composition of determinant maps removes those choices.
The remaining equations are precisely the established frame identity and
composition laws. This is internal derived API for actual determinants; it
asserts neither ampleness nor representability of parabolic subgroups.
