# Compact reindexing for the same Levi subgroup

The construction `compactPictureReindex` uses two presentations of the same
Levi subgroup in an ambient group. It takes an identification inducing the
identity on ambient points and an equivalence of the inducing
representations over that identification. It acts on compact sections
pointwise by the inducing equivalence, as `compactPictureReindex_eval`
shows. The source parabolic, its radical and the compact subgroup are
shared by the two presentations.

With one quotient measure, `domain_eq_top_reindex` transports full weak
convergence by `domain_eq_top_iff_equiv`. Given compatible compact
coordinate maps and an equivalence of the twisted inducing
representations, `compactIntegral_reindex_square` compares operators
satisfying the two full weak integral specifications. It uses
`HasIntegral.map_induced` and uniqueness of the smooth weak integral at
each point of the compact subgroup. The identity uses the same measure
on both sides. This is the coordinate comparison for the compact form of
the standard integral in Waldspurger IV.1 and the factors of V.1.
