# Power quotients from an open subgroup

Authors: Worker 450 and Worker 107.

This internal construction supports the actual idele-class power-quotient proof.
Worker 107 proposed the open S-unit subgroup route and its generic interface;
Worker 450 implemented the map, kernel identity, and topological transfer.
For a commutative group `G`, subgroups `P` and `H`, and natural `m`, the map
`openSubgroupPowerClassMap P H m` sends an `m`th-power class in `H` to its class
in `(G/P)/(G/P)^m`. All quotient topologies are the existing quotient topologies.
The map is induced by the inclusion of `H` and the quotient by `P`.

If `P ⊔ H = ⊤`, `subgroupClassMap_surjective` proves that the inclusion of `H`
surjects onto `G/P` by writing each element of `G` as `p*h`. Consequently
`openSubgroupPowerClassMap_surjective` proves that the induced map on power
quotients is surjective. `openSubgroupPowerClassMap_ker` identifies its kernel
with exactly the image of `P.subgroupOf H` in `H/H^m`: if the class of `h` in
`G/P` is the `m`th power of `c`, lift `c` to `a` in `H`, and replace `h` by
`h/a^m`. This element lies in `P ∩ H` and has the same class as `h` in `H/H^m`.

For a commutative topological group, `openSubgroupPowerClassMap_continuous`
proves continuity by the quotient topology. If `H` is open, the composite of
its inclusion and the two quotient maps is open, so
`openSubgroupPowerClassMap_isOpenMap` proves that the induced map is open.
Together with `P ⊔ H = ⊤`, this gives the open quotient map recorded in
`openSubgroupPowerClassMap_isOpenQuotientMap`.

The helper `openQuotientHom_profinite_of_finite_kernel` considers an arbitrary
open quotient group homomorphism from a compact Hausdorff totally disconnected
space to a topological group, with finite kernel. The kernel is closed because
the source is Hausdorff. Its equality with the preimage of the identity and the
quotient-map property show that the identity singleton in the target is closed,
so the target topological group is Hausdorff. Compactness follows from
continuous surjectivity. To separate distinct target points `x` and `y`, lift
`x` to `a`, choose a clopen neighborhood of `a` inside the preimage of the
complement of `{y}`, and take its image. This image is open because the map is
open and closed because it is compact in the now Hausdorff target. It contains
`x` and excludes `y`. Thus the target is totally separated, hence totally
disconnected.

`openSubgroupPowerQuotient_profinite` combines this transfer with the exact
kernel identity. Its hypotheses are that `H` is open, `P ⊔ H = ⊤`, `H/H^m`
is Hausdorff, compact, and totally disconnected, and the image of
`P.subgroupOf H` in `H/H^m` is finite. No positivity of `m` is needed when
that finite image is supplied directly.

For `0 < m`, `subgroupPowerClassImage_finite_of_fg` proves the finite-image
hypothesis from finite generation of `P.subgroupOf H`. The image is finitely
generated as the homomorphic image of that subgroup and is torsion because
every element of `H/H^m` has order dividing `m`. Mathlib's finiteness theorem
for finitely generated torsion abelian groups therefore makes the image finite.
The final wrapper `openSubgroupPowerQuotient_profinite_of_fg` concludes all
three topological properties for the actual double quotient `(G/P)/(G/P)^m`.

These are internal consequences of elementary quotient-group algebra and
Mathlib's quotient, compact-space, clopen-basis, and finitely generated abelian
group results. They implement the topology step of the agreed S-unit route to
the published `Langlands.Global.IdeleClassPowerQuotientProfiniteStatement`;
they assert no arithmetic facts about S-units or local multiplicative groups.
In the intended application, the arithmetic work supplies the open subgroup,
its profinite power quotient, the generation condition, and finite generation
of the intersection. The helper assumes no norm-one compactness or
class-field-theory package.
