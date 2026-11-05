# A compact integral family independent of a closed representation

Author: Worker 1641.

For an affine group scheme of finite type over a number field `F : Type u`,
`FiniteTypeIntegralFamily.subgroup F G v` chooses one closed finite dimensional
representation using the published `affineLinearEmbeddingStatement`, then
takes the representation-integral subgroup from `LinearIntegralFamily`.
The dimension and representation depend only on `F` and `G` and their stated
instances. They are chosen before any finite place, adelic point or regular
function. The required instances are `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`; no model or representation is supplied as
an additional mathematical premise.

The three direct consequences are compactness at every finite place,
eventual membership of each actual finite adelic point under the literal
coefficient projection, and uniform integrality for each global regular
function. Compactness uses affineness of the underlying scheme, deduced
from affineness of its structure morphism. The other consequences apply
the corresponding representation-integral results.

`LinearIntegralFamily.eventually_subgroup_le` compares a closed
representation `ρ` with any finite dimensional representation `σ`.
The forward and inverse entries of `σ` are global regular functions on
the actual general linear group. Pull them back to `G` and apply uniform
integrality on the `ρ` subgroup to each of the finitely many functions.
Outside the union of their finite exceptional sets, every member of the
`ρ` subgroup belongs to the `σ` subgroup. If both representations are
closed immersions, applying the comparison in both directions proves
`eventually_subgroup_eq`. In particular the chosen family agrees with
the family from any other fixed closed representation at cofinitely
many places. The result compares actual subgroups, not only isomorphism
classes or conjugacy classes.

This is an internal consequence of the published closed-linear-embedding
theorem and the finite-coordinate denominator argument in
`LinearIntegralFamily`. The latter is derived from Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Lemma 2.4.7 and
Proposition 2.4.10, printed pp.60–62 / PDF pp.77–79, registered source
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The registered October 2026 errata, SHA256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
does not change those passages. Representation independence here is a
derived actual-point statement, rather than a verbatim source assertion.

No maximal compactness or parabolic covering is asserted in this module.
The good-model and local structural obligations in
`IntegralIwasawaFamily.ExistenceStatement` remain.
