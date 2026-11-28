# Chevalley's theorem for commutative groups over algebraically closed fields

`Langlands.AbelianScheme.CommutativeChevalleyStatement` states that a
smooth connected commutative group scheme `G` of finite type over an
algebraically closed field `k` admits an abelian variety quotient. Smoothness
and quasi-compactness of the structure morphism give finite type, and
`ConnectedSpace G.X.left` expresses connectedness of the underlying scheme.

The proposition supplies an `AbelianScheme` over `Spec k` and a homomorphism
`q` of commutative group schemes from `G` to its underlying group scheme.
The underlying scheme morphism of `q` is smooth and surjective.
`CommGroupScheme.kernel q` is the fibre of `q` over the identity section.
Its structure morphism is smooth and affine, and its underlying scheme is
connected.

This is the existence assertion of Bosch, Lütkebohmert and Raynaud,
*Néron Models* (Springer, 1990), §9.2, Theorem 1 and the following paragraph
on Chevalley's algebraically closed case, printed p. 243 (PDF p. 250),
specialized to commutative groups. The source's smooth connected linear
subgroup `L` gives the affine kernel of `G → G/L`. The quotient projection
is an fppf torsor under `L`, so it is locally a projection with smooth fibre
`L` and is smooth and surjective. The abelian variety `G/L` gives the smooth,
proper and geometrically connected commutative group scheme in the conclusion.

The registered source is `bosch-lutkebohmert-raynaud-1990-neron-models`,
SHA-256 `16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
