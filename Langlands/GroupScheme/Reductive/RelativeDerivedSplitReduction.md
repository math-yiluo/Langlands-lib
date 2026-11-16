# Relative derived-group existence from split affine models

This internal reduction connects the published affine pinned étale atlas to
admissible-subgroup descent and the full-kernel construction. It retains two
explicit inputs: relative semisimple fppf-perfectness and existence of the
required subgroup, or equivalently of a suitable torus quotient, on every
supplied split affine pinned model. It does not prove either input or the
unconditional relative derived-group existence theorem.

`RelativeDerivedSplitExistenceStatement` asks, for every
`AffinePinnedModel M`, for a group scheme `D` over `M.base` and a homomorphism
`d : D ⟶ M.group` satisfying the unchanged `RelativeDerived.IsAdmissible`
predicate. Thus the inclusion is closed and normal on every relative test
scheme, `D` is reductive with semisimple geometric fibres, and its represented
fppf quotient in `M.group` is a relative torus. The supplied model includes a
commutative coefficient ring, finite coordinate and root types, a closed
fibrewise maximal coordinate split torus, the full reduced fibrewise root
datum, free rank-one actual root Lie spaces, a root-datum base, and pinning
trivializations. No quotient or derived subgroup is included in that data.

`RelativeDerivedSplitTorusQuotientExistenceStatement` instead asks for a group
scheme `Q` over `M.base` and a homomorphism `q : M.group ⟶ Q` satisfying
`RelativeDerived.IsSemisimpleTorusQuotient`: the target is a relative torus,
the map is smooth and scheme-surjective, and every full geometric kernel is
semisimple. `relativeDerivedSplitExistence_iff_torusQuotient` proves equivalence
of these two inputs by the existing kernel construction and its converse.
It adds no assumption on the coefficient ring, including its characteristic
or whether it is the zero ring.

The helper `RelativeDerived.IsAdmissible.comp_iso` transports an admissible
inclusion through an actual ambient group-scheme isomorphism. Closedness
transports with the inclusion, and normality is the inverse image under the
inverse isomorphism. The source group and its geometric fibres are unchanged.
For its quotient, precompose the supplied quotient map by the inverse ambient
isomorphism. `IsFppfQuotient.of_iso_square` identifies its full all-test kernel
with the transported range and preserves flatness, local finite presentation
and scheme surjectivity.

`relativeDerivedGroupExistence_of_split` chooses the published
`AffinePinnedAtlas.ofReductive` for the given arbitrary-base reductive group.
Each chart has an actual isomorphism from the pullback of that group to its
supplied affine pinned model. Apply the split existence input to the model,
and transport its inclusion back along the chart isomorphism. These local
admissible inclusions lie over the atlas's actual jointly covering étale
family. `relativeDerivedAdmissibleEtaleDescent` then constructs a global
admissible inclusion, using the explicit perfectness premise for overlap
matching. Coverage and pinning existence come from the published atlas;
there is no new local splitting assumption or finiteness condition on the
base or cover.

`relativeDerivedGroupExistence_iff_split` supplies the converse by evaluating
the original existence proposition on each model's base and reductive group.
`relativeDerivedGroupExistence_of_splitTorusQuotient` combines the split
kernel equivalence with the descent reduction. All statements and proofs are
polymorphic in the arbitrary universe `u`.

The provenance is internal. These results are composites of the unchanged
published existence and admissibility interfaces, the affine pinned atlas,
ambient and quotient transport, full scheme kernels, and conditional étale
descent. They introduce no new literature claim. The original target and its
imported statements are preserved; the two geometric existence inputs remain
separate proof obligations.
