# Structural steps for induced reciprocity representations

Author: Worker 1646. Internal helper for task
`f096b984-dff5-4425-861f-8f298e5896fb`, toward the exact published target
`Langlands.ClassField.Global.RelativeWeilGroup.WeakInductionAssociationStatement`.
This module proves structural consequences of the existing constructions. It
does not prove weak association or assume an unproved reciprocity statement.

The fields and the representation carriers retain independent universes. The
character need not be unitary. The results require the published restriction
compatibility of the class family, but no arithmetic normalization.

`ExactGrothendieckGroup.continuousInduceAlong_ofRepresentationWithProof` identifies the
continuous exact class obtained by induction with the class of the actual
algebraic `FiniteRepresentation.induceAlong`. Both constructions first restrict
along the inverse from the image subgroup and then induce from that subgroup.
The proof applies the existing restriction and induction formulas on genuine
classes; all continuity certificates are the published ones.

`index_range_restrictionInclusion` proves that the image of the intermediate
relative Weil group has index `[E' : F]`. The published
`range_restrictionInclusion` and surjectivity of `projection` reduce this to the
index of `Gal(L/E')` inside `Gal(L/F)`. Restriction of scalars identifies the first
group with its image. The formula `index * subgroup cardinality = group
cardinality`, the Galois cardinality theorem, and the tower law for dimensions
then give the claimed index.

`inducedReciprocityRepresentation_rank` combines this result with the published
`FiniteRepresentation.rank_induceAlong` and `characterLine_rank`.

`inducedReciprocityRepresentation_isContinuous_discrete` uses the proved
continuity of `continuousReciprocityCharacter`, the continuity of its character
line, and `isContinuous_induceAlong` along the published open embedding
`restrictionInclusion`. `inducedReciprocityRepresentation_class` applies the
general exact-class comparison to this character line.

`inducedReciprocityRepresentation_isContinuous` reads that continuity result in
the default Krull topology. The published
`krullTopology_eq_relativeGaloisTopology` identifies the two topologies on the
finite Galois group; replacing the topology instance preserves the underlying
representation.

These lemmas are derived from the Library constructions for this task. Their
proofs use only elementary group index and finite-dimensional linear algebra,
not local Langlands, globalization, or a global functional equation. They leave
the target and its imports unchanged.

`continuousInducedReciprocityRepresentation` bundles the actual induced
representation with the continuity just proved. It is a genuine object of the
continuous exact virtual group, with its original carrier and action.
