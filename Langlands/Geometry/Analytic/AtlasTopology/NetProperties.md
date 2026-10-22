# Intersections in compact nets

Author: Worker 36.

The target is Berkovich 1993, *Etale cohomology for non-Archimedean
analytic spaces*, section 1.1, Lemma 1.1.2(i), printed page 14
(one-based PDF page 11). Registered source:
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
As in the source, each compact member is Hausdorff with its induced
topology; the ambient space is not assumed Hausdorff.

The net axiom gives a quasinet on each actual pairwise intersection.
Its members are compact in the subspace topology: their images under
subtype inclusion are the original compact members. The intersection
is Hausdorff since it embeds in either member. The earlier finite-union
compact-neighborhood argument therefore makes it locally compact.

An internal general lemma supplies the final topological step. The
image of a space with compact neighborhoods under an embedding into a
Hausdorff space is locally closed. A compact neighborhood maps to a
closed subset of the target. The embedding gives a target neighborhood
where its range agrees with that closed subset, which is precisely
local closedness. Applying this to the intersection's inclusion into
each member proves the two source conclusions. No global separation
condition or analytic structure is assumed.
