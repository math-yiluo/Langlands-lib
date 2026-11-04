# Dynamic unipotent bounds from an actual homogeneous quotient curve

This internal construction specializes the homogeneous-curve orbit bound to
actual dynamic identity-limit subgroups. It works over an algebraically
closed field in universe `u`, in every characteristic.

The inputs are an explicit proof of
`AlgClosedReductiveNormalSolvableTorusStatement`, a pseudo-reductive ambient
group `G`, a solvable closed subgroup `b : B ⟶ G`, a split torus `T` mapping
to `B`, and a cocharacter `ν` of `T`. A supplied quasi-compact smooth
surjective quotient `q : G.X ⟶ Q` has exact all-test fibers equal to the
right cosets of `B`; its target is separated and has topological Krull
dimension at most one. The dynamic group `U_G(ν)` is assumed not to lie
in the range of `B`, as an inclusion of all-test subgroup functors.

`curveUnipotentData` constructs an actual smooth connected affine unipotent
group representing `U_G(ν)`, its closed inclusion into `G`, an actual
moving rational orbit on `Q`, and the bound on its actual Lie dimension
by one. To do so it also constructs the canonical affine representative of
`U_B(ν)` and the actual induced closed inclusion into the representative
of `U_G(ν)`. This inclusion commutes with the ambient inclusions; equality
of tangent dimensions is never used to compare incomparable subgroups.

Smoothness of `B` follows from its identification with the actual identity
fiber of the smooth quotient, and it is affine because it is closed in
`G`. The canonical dynamic groups are smooth and connected by the
published dynamic results. Their unipotence follows from the actual
closed unitriangular embedding, unipotence of standard unitriangular
groups, and inheritance of unipotence by closed subgroups. The exact
quotient dimension formula bounds `dim Lie(G) - dim Lie(B)` by one.
The signed dynamic dimension formula then bounds
`dim Lie(U_G(ν)) - dim Lie(U_B(ν))` by one.

The actual `U_B(ν)` inclusion has composite range contained in `B`.
The homogeneous-curve result therefore applies to these two groups and
gives `dim Lie(U_G(ν)) ≤ 1`. The constructed representative identifies
this with the intrinsic dynamic tangent bound. The last theorem applies
the disjoint-weight-space argument to conclude equality of any two
positive roots for this cocharacter.

The construction composes existing Library constructions and proofs and
is internal rather than a formalization of a new external source.
The normal-solvable-torus theorem, quotient existence, its curve dimension,
and the specified noncontainment remain explicit inputs. The full
rank-one positive-root uniqueness theorem remains open.
