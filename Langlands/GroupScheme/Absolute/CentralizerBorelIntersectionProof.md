# A Borel subgroup of a cocharacter centralizer in a prescribed ambient Borel

Authors: Worker 1438, Worker 1479 and Worker 898.

`Langlands.GroupScheme.centralizerBorelIntersection.{u}` proves exactly the
unchanged published `CentralizerBorelIntersectionStatement.{u}`. It uses the
published `solvableProperFixedPoint` theorem and
`IsBorelSubgroup.centralizer_product_isClosed` without retaining an extra
fixed-point, conjugacy or quotient-existence premise.

The proof has exactly the target's hypotheses. The universe and characteristic
are arbitrary. The
cocharacter can be trivial or noninjective, and the specified closed map
`j : M → G` represents its full dynamic centralizer. The ambient group is
smooth, connected and affine, and `M` has the target's explicit smoothness
and connectedness. The Borel is the specified map `b : B → G`, whose
range contains the cocharacter on every relative test scheme.

The witness is the actual pullback intersection `subgroupIntersection j b`,
with its first projection to `M`. The published intersection geometry
supplies a closed smooth solvable subgroup. To obtain connectedness,
restrict the cocharacter to this particular `B`. The second projection
represents its dynamic centralizer inside `B`, so the published
`dynamicConnected` theorem applies. This retains all relative scheme
tests.

Choose the actual smooth homogeneous quotients `Q` of `G` by `B` and `R`
of `M` by this intersection, with the published constructions. Their maps
are smooth, surjective and quasi-compact and have the exact right-coset
fiber criterion on every relative test scheme. The published
`IsBorelSubgroup.quotient_isProper_of_solvableProperFixedPoint` applied to
`solvableProperFixedPoint` makes this very `Q` proper.

The supporting theorem `IsBorelSubgroup.centralizer_product_isClosed`
gives closedness of the actual multiplication image of `M × B` in `G`,
without a remaining splitting, conjugacy or quotient-existence premise.
The published closed-product comparison then proves properness of `R`.
Apply
`properSolvableQuotientBorel_of_solvableProperFixedPoint solvableProperFixedPoint`
to its actual projection and exact fibers. This proves that the first
intersection projection is Borel in `M`.

Finally, `range_subgroupIntersectionHom` identifies the ambient range of
the composite with the intersection of the ranges of `j` and `b`.
Projection to its second factor proves the desired containment on every
test scheme, including nonreduced and nonaffine schemes.

The provenance is an internal assembly of the named Library
constructions. It copies the intersection argument of
`IsBorelSubgroup.centralizer_intersection_isBorel_of_closed_product`,
replacing its two global quotient inputs by the prescribed-Borel and
proper-solvable-quotient reductions from the same fixed-point statement.
Worker 1479 supplied the intersection geometry and connectedness argument;
Worker 898 supplied the prescribed-Borel quotient route. The fixed-point
theorem is imported from Worker 1364's published proof, and the product
closedness proof reuses Worker 1333's same-source conjugacy route.
No imported statement or its documentation is changed.
