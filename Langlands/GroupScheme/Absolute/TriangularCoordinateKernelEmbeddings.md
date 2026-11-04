# Closed additive embeddings of actual coordinate quotient kernels

This internal construction works over any field `k : Type u`. Every use of
`AffineHomImageStatement.{u}` is an explicit premise. No smoothness,
connectedness or reducedness is assumed for the source or its subgroup kernels.

`exists_closed_additive_embedding` starts with an actual affine group scheme
`K` locally of finite type, an additive coordinate `c : K → Ga`, and an actual
fppf quotient `q : K → Q` by the full kernel of `c`. It assumes that `q` is
quasi-compact. Applying the image premise to `c` gives a closed inclusion
`i : J → Ga` and a quotient `r : K → J` by the same full kernel. The
published `FppfQuotientComparison.iso` identifies `Q` with `J`; composing its
forward isomorphism with `i` produces a closed inclusion `a : Q → Ga`
satisfying `q ≫ a = c`. Quasi-compactness of `r` follows from the affineness
of its source and target. The standard polynomial additive group supplies the
finite-type and affine target geometry.

`QuotientTerm.exists_kernelEmbedding` applies this construction to two supplied
quotients `A = H/F` and `B = H/E`, with `E ≤ F`. The larger subgroup `F` is
represented by an affine, locally finite type group scheme `K → H`. A supplied
coordinate on `K` has full kernel exactly `E.comap i`. The actual restriction
`K → ker(B → A)` is fppf by the cartesian restriction theorem in
`TriangularCoordinateQuotients`. Its quasi-compactness is the base change of
that of `B`'s quotient map. Its full kernel is the supplied coordinate kernel,
so the generic construction embeds the actual comparison kernel as a closed
subgroup of `Ga`, with the stated factorization.

`isRepresentedBy_seriesHom` records that each actual closed series inclusion
represents its full range. For `N > 0`, `seriesCoordinate` uses the genuine
entry coordinate in row `t % N` and column `t % N + t / N + 1` when that
column belongs to `Fin N`; otherwise it is the zero homomorphism.
`range_kernel_seriesCoordinate_all` shows in both cases that its full kernel,
mapped into `H`, is the next series term. The genuine-coordinate case uses
the previously proved coordinate-kernel identity; the zero case uses equality
of the repeated terms and the all-test kernel criterion for the zero map.
An equality of coordinates is transported through the ambient range expression,
so no choice of a point in a quotient is made.

`range_kernel_seriesCoordinate_comap` uses the monic current inclusion and
the adjacent containment to identify that internal full kernel with the
inverse image of the next series term. Finally,
`exists_series_kernelEmbedding` applies the generic quotient result to the
two supplied series quotients. Their actual comparison kernel is closed in
`Ga`, and its coordinate pulls back to `seriesCoordinate`. All identities
are identities of subgroup functors on every scheme over `k`.

The content is derived from the published image and quotient interfaces,
explicit matrix coordinates and categorical comparison. It does not prove the
image-existence premise, construct the quotient schemes, descend conjugation,
or construct a splitting section. Its series specializations explicitly assume
`N > 0`; the size-zero endpoint is a separate tower obligation.
