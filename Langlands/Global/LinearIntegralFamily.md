# Integral families from actual closed linear embeddings

Author: Worker 1641.

This internal construction is a prerequisite for the integral Iwasawa family
proof. For a number field `F : Type u`, an actual group scheme `G` over `F`
and an actual finite dimensional representation `ρ`, `subgroup F G ρ v`
is the inverse image, under `ρ.affineMatrix`, of the existing integral
matrix subgroup at the finite place `v`. Both the matrix and its inverse
must have entries in the literal valuation subring
`v.adicCompletionIntegers F`. The carrier is the published `G.affinePoints`
and its topology is the published regular-function evaluation topology.

`eventually_projection_mem` proves eventual membership for every actual finite
adelic point. There are finitely many forward and inverse matrix entries.
Each is an actual finite adele, and its defining restricted-product property
gives integrality away from finitely many places. Finite conjunction combines
these exceptional sets. Naturality of the actual representation identifies
the resulting matrices with the coefficient-map projections appearing
literally in `IntegralIwasawaFamily.IsIntegralIwasawaFamily`.

When the underlying representation is a closed immersion and `G` is affine,
`isCompact_subgroup` proves compactness at every finite place. The actual
point map of a closed immersion is a closed embedding for the evaluation
topology. The existing general linear point homeomorphism identifies its
target with the matrix units topology. The integral matrix subgroup is
compact because the canonical completed integer ring is compact. Compactness
therefore pulls back along this closed embedding.

`eventually_uniform_integral` proves the regular-function conclusion with
the exceptional set depending only on the function. Surjectivity on affine
global sections lifts the function to a function on the general linear
group. The explicit coordinate ring of that group is a quotient of a
polynomial ring in forward and inverse matrix entries, so choose a polynomial
lift. Induction on that polynomial uses eventual integrality of every fixed
coefficient of `F`, integrality of both kinds of matrix entry on the subgroup,
and closure of the valuation subring under sums and products. Thus the same
finite exceptional set works for all subgroup members.

This is a derived finite-coordinate and denominator argument underlying
Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Lemma 2.4.7 and Proposition 2.4.10, printed pp.60–62 / PDF pp.77–79.
Registered source `getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
All five pages of the registered October 2026 errata
`getz-hahn-2024-errata-2026-10`, SHA256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
were read; no entry changes these passages.

This construction does not assert maximality or a parabolic product
decomposition. Those require eventual good reductive and parabolic models
and their local structural theorems. Consequently these results do not prove
`IntegralIwasawaFamily.ExistenceStatement`.
