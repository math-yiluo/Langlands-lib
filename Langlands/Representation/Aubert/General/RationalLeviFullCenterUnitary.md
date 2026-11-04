# Unit modulus on the full actual Levi center

Worker 480.

This is an internal derived construction for the zero-modulus case of the
rank-one self-association argument. It extends unit modulus of a smooth
character from the literal Levi-central torus points to the full abstract
center of the same actual Levi. The extension retains actual split-component
and compactness inputs. It does not prove their existence or the self-association
target.

The generic theorem
`Langlands.PositiveCharacter.norm_eq_one_of_compact_quotient` concerns a
topological group `H`, a normal subgroup `K`, the canonical quotient topology,
and a compact quotient `H / K`. If a complex-unit character has open kernel
and has norm one on `K`, its positive norm character descends through `K`.
The quotient-map criterion makes the descended kernel open.
`Langlands.PositiveCharacter.eq_one_of_compact` then makes the descended
character trivial, giving norm one on every element of `H`.
No closedness assumption on `K` or Hausdorff assumption on the quotient is used.

In the namespace
`Langlands.Aubert.General.RationalPointFamily`,
`surjective_leviSchemeCenterToCenter` proves surjectivity for every represented
standard Levi `M` that is connected reductive over a nonarchimedean local
field `k`. The map is precisely `standardLeviSchemeCenterToCenter` at
`rootSet i ν I`. Pull an abstract central point back along
`Subgroup.centerCongr (standardLeviRationalPointsEquiv ...)`.
The published theorem `Langlands.GroupScheme.rationalCenterComparison`
puts that point in `schemeCenterPoints M`. The forward equivalence maps it
back to the original point. This uses the reverse full-center comparison,
rather than only scheme-center inclusion.

`leviCentralCharacter_norm_eq_one_of_splitComponent` accepts an actual
representation `j : M → G` of the same all-test standard Levi, an actual
split component `a : A → M`, and a factorization `g ≫ i = a ≫ j` through
the same torus `T`. It also accepts
`CenterSplitComponentCompactness M hM A a ha`, an open-kernel character
on `Subgroup.center (levi i ν I)`, and unit modulus on every element of
`leviCentralTorusPoints i ν I`. Its conclusion is unit modulus at every
element of the full abstract Levi center.

The proof pulls the character back to `schemeCenterPoints M`.
Continuity of this forward center map follows from
`continuous_rationalPointMap` and the two subgroup topologies; no inverse
topology comparison is required. The topology of `M(k)` is the canonical
`rationalPointTopology`, and the topology of `G(k)` is `pointTopology`.
Connected reductivity supplies smoothness and affineness, so
`rationalPoint_isTopologicalGroup` gives the required topological group.
On a point in the actual image `centralRationalPointImage a`, the
factorization identifies its ambient value with the image under `i` of a
point of `T(k)`. It is central in the literal Levi and hence belongs to
the named Levi-central torus subgroup. The supplied unit-modulus law
therefore applies to this point, with equality verified through both
subtype layers. The generic theorem applies to the actual image subgroup
and its canonical quotient topology. Surjectivity of the full-center
map gives the conclusion at every abstract central point.

`leviCentralCharacter_norm_eq_one_of_structural_statements` chooses the
canonical representative `Standard.leviScheme` and its inclusion.
`StandardLeviSplitComponentStatement` supplies its connected reductivity,
split component and factorization through `T`.
`CenterSplitComponentCompactnessStatement` supplies the needed compactness.
The wrapper uses the actual maximal split torus and generic cocharacter;
it has no rank, characteristic or maximal-index restriction.

Finally, `leviUnitaryCentralCharacter_of_centralTorus` packages the result
with a supplied scalar-action law into `UnitaryCentralCharacter ρ`.
The group-scheme and representation-carrier universes are independent.
This construction supplies no scalar-character existence, admissibility,
representation unitarizability or induction irreducibility. The two named
structural statements remain proof obligations when this helper is used
to prove the exact unapplied self-association proposition.

The provenance is derived: the argument combines the published actual
point/center maps and full-center equality with positive-character
triviality on compact groups, quotient lifting and the displayed actual
factorization. It uses no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem.
