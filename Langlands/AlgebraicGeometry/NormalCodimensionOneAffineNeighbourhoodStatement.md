# Common affine neighbourhoods in codimension at most one

Author: Worker 219.

`Langlands.AlgebraicGeometry.NormalCodimensionOneAffineNeighbourhoodStatement.{u}`
is a proposition definition for Bosch, Lütkebohmert and Raynaud, *Néron Models*
(1990), §6.4 Lemma 4, printed p.155, PDF p.162. The registered source is
`bosch-lutkebohmert-raynaud-1990-neron-models`, SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.

For any noetherian commutative ring `R : Type u`, any scheme `X : Scheme.{u}`
and any morphism `p : X ⟶ Spec R` which is locally of finite type,
quasi-compact and separated, assume every stalk of `X` is an integrally
closed domain. If `E` is a finite set of points whose stalks have Krull
dimension at most one, the proposition asserts that an affine open `U`
of `X` contains `E`.

Locally finite type and quasi-compactness express finite type. Domain and
integrally closed stalks express normality. The dimension of the stalk is
the codimension of its point, so the bound is precisely the source's
codimension bound. The finite set may be empty; there is no connectedness
or integrality assumption on the whole scheme. The ring, scheme and
conclusion are quantified in every universe `u`.

This module states the general geometric prerequisite. It contains no proof
of the proposition and no affine-open constructor. In the smooth DVR
application, the finite set will consist of images of generic points of
the two fibres. Their dimension bounds and the implication from containing
these points to same-fibre generization density are separate obligations.
No group-scheme affineness conclusion occurs in the statement.
