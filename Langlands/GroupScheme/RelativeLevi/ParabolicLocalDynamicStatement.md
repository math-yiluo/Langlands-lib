# Relative parabolic subgroups are etale-locally dynamic

Author: Worker 589.

`Langlands.GroupScheme.RelativeParabolicEtaleLocalDynamicStatement.{u}` states that
for any scheme S, reductive group scheme G over S and relative parabolic i : P → G,
there is an etale covering family U_a → S and a cocharacter of G over each U_a whose
dynamic parabolic is represented by the base change of the actual homomorphism i.
Representation means monicity and equality of subgroup functors on every test scheme.
The statement does not assume i to be closed and does not prove this local description.

The source is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
Proposition 5.2.3 and its proof, PDF/printed pp.152–153; Definition 5.2.1 is on p.151.
The proposition supplies an etale-local maximal torus in P. After a further etale
localization this torus is split, and the final assertion supplies a local cocharacter
with P = P_G(lambda). Composing these etale and Zariski covering families yields the
cover in the Lean statement. The cocharacter is recorded only in G; no choice of its
torus factorization is part of this target.

This is a prerequisite for the closedness target. The separate reduction module proves
that the statement implies `RelativeParabolicClosedStatement` using the already published
closed representability of dynamic subgroups and descent. It neither assumes nor uses
that closedness target as a theorem. The base may be empty, non-affine or non-noetherian;
all schemes and the cover index type are in universe u.
