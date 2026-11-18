# The projected parabolic compact subgroup of the Levi

This internal construction isolates the compact subgroup available on the
source Levi from an arbitrary original ambient Iwasawa pair. It is derived
from the existing semidirect decomposition and elementary topology; it
introduces no original-literature assertion.

For the original semidirect decomposition `P = M U` and subgroup `K` of the
ambient group, `projectedLeviCompact h K` is exactly the image of
`K.subgroupOf P` under the original Levi projection `h.projection`. It is a
subgroup of `M`, retaining the original `K` and projection. The theorem
`subgroupOf_le_projectedLeviCompact` proves that it contains the original
literal intersection `K` with `M`: the projection is the identity on `M`.

`isIwasawaPair_projectedLeviCompact` assumes a subgroup `P0` contained in
`P`, containment of `U` in `P0`, and the original factorization `G = P0 K`.
It proves `M = (P0 in M) projectedLeviCompact`. For `m` in `M`, factor its
ambient value as `p k`. The factor `k` belongs to `P`, so its projection is
in the displayed image subgroup. The projection of `p` belongs to `P0`
because its quotient from `p` is unipotent. Applying the original projection
to the product recovers `m`. There is no assumption that the projection
carries `P` intersect `K` back into `K`.

`isOpen_projectedLeviCompact` uses the original openness of `K` and the
proved containment of the open literal Levi intersection. For a closed
parabolic and the displayed continuous Levi projection,
`isCompact_projectedLeviCompact` proves compactness from compactness of `K`:
the projected subgroup is precisely the continuous image of the compact
literal parabolic intersection. Neither result replaces this image by the
possibly smaller intersection `K` with `M`.

The first two results are group-theoretic. Openness is stated in a topological
group, and compactness requires only the topology, the displayed continuity
and closedness. These are implications about the actual supplied data;
no geometric existence theorem is assumed or concluded.

In a rational standard-parabolic application, the published actual semidirect
decomposition, minimal-parabolic containment, unipotent containment,
closedness and continuous projection supply these inputs. This provides a
compact open Iwasawa factor on the source Levi even when its original
intersection with `K` has no proved Iwasawa property. Adapting an existing
coefficient or spherical-function consumer from that original intersection
to the projected subgroup remains separate. No equality of the subgroups,
Xi identity, analytic coefficient estimate, or wave-packet theorem is
asserted here.
