# Central unitarizers on actual rational points

This internal construction applies `CentralUnitarization.centralUnitarizer` to
the actual map `(Plancherel.rationalCharacterValuation G).rangeRestrict`. Its
target is the actual integer-valuation image of the algebraic rational
characters of `G`. The group is `GroupScheme.rationalPoints G`, with the
canonical `rationalPointTopology F G.X`. The field is any nonarchimedean local
field, with no characteristic restriction. The affine finite-type hypotheses
are explicit. The field universe `u` and representation-carrier universe `v`
are independent.

`rationalCentralUnitarizer` constructs a positive character with open kernel
from a smooth complex scalar character of the full abstract center of `G(F)`.
Besides this character, its inputs are an actual central morphism
`s : T.toGrp ⟶ G`, finite index of `RenardCartan.splitValuationImage s` in
`rationalCharacterValuationImage G`, and compactness of the common norm kernel
restricted to the full abstract center. The construction needs centrality of
`s`, rather than an unproved assertion that it is a split component.

`finiteIndex_rationalCentralValuationImage` places every actual point coming
from `s` in the abstract group center by `GroupScheme.IsCentral.range_le_center`.
Its valuation therefore belongs to the full central valuation image. A
supergroup of a finite-index subgroup has finite index, by
`Subgroup.finiteIndex_of_le`. This argument needs no equality between the
scheme-center points and the abstract center of the rational-point group.

`rationalCentralValuation_ker` identifies the kernel of the valuation projection
restricted to the abstract center with
`(rationalCommonNormKernel G).subgroupOf (Subgroup.center (rationalPoints G))`.
It uses `MonoidHom.ker_rangeRestrict` and
`Plancherel.rationalCharacterValuation_ker`. The ambient open-kernel input is
discharged by `Plancherel.isOpen_rationalCommonNormKernel`, which uses actual
compact open subgroups of the canonical rational-point topology.

The generic central unitarizer now applies. Its construction descends the
modulus of the scalar character across the compact central kernel, extends
that positive character across finite index, and pulls back its inverse.
`rationalCentralUnitarizer_restrict` states that its central restriction is
the inverse modulus of the supplied scalar character.
`isOpen_ker_rationalCentralUnitarizer` proves openness of its kernel.
`rationalTwistUnitaryCentralCharacter` constructs the existing
`UnitaryCentralCharacter` datum on the actual same-carrier scalar twist.
The resulting central character is the supplied character divided by its
modulus.

`exists_rationalPositiveTwist_unitaryCentralCharacter` uses the published
`admissibleSchur_centralCharacter` to supply the scalar character for every
irreducible admissible complex representation. It retains the compactness and
finite-index assumptions above. It asserts a norm-one scalar central action,
without asserting an invariant positive form on the whole representation.

This is a derived adapter, not a claim from an external source. Its
representation-theoretic inputs are the actual admissible Schur theorem and
the generic central unitarizer; the latter uses compact positive-character
triviality and finite-index positive-character extension. No Langlands
classification, representation-character independence, geometric lemma,
adjointness or cuspidal-support theorem is used in these proof bodies.

The remaining structural inputs are explicit. In particular compactness of the
norm kernel on the scheme-center points alone does not supply compactness on
the full abstract center. That use would additionally need the reverse
scheme-center comparison. Finite index of the character-restriction lattice
alone is not substituted for finite index of the actual point-valuation
image. This construction does not prove either of those structural claims or
`RationalRankOneSelfAssociationStatement`.
