# Restricting topological inputs to an actual Levi

Author: Worker 1343.

This is an internal construction used to apply actual standard-family
induction compatibility to Corollary 1.10(a). It proves elementary
topological inheritance for literal subgroup intersections. It does not
assert any finite-length preservation or Aubert identity.

`subgroupOfToAmbient U L` is the actual homomorphism from `U.subgroupOf L`
to `U` obtained by forgetting membership in `L`. It is continuous and,
when `L` is closed, is a closed embedding: its range consists exactly of
the elements of `U` that belong to `L`.

`restrictedCompactSubgroup U L K` is the inverse image of the subgroup
`K ≤ U` under that homomorphism. If `K` is compact and `L` is closed,
the inverse image is compact by the closed-embedding compact-preimage
theorem. Given a compact subset of `U.subgroupOf L`, map it to `U`,
place it in a compact subgroup using
`Jacquet.Localization.IsLimitOfCompactSubgroups U`, and take the inverse
image. This proves `isLimitOfCompactSubgroups_subgroupOf`, without an
openness assumption on `L`.

For an ambient semidirect decomposition `P = M ⋉ U` and its literal
restricted decomposition inside `L`, `projection_subgroupOf` identifies
the two projections on underlying elements. The proof uses the
published `projection_eq_iff` characterization and the restricted
`projection_inv_mul_mem`. Continuity then follows by composing with
the ambient projection and using the embedding of the restricted
Levi into `M`.

The two `RationalPointFamily` specializations use the actual published
standard subgroups and the canonical rational-point topology.
`standardLeviUnipotent_isLimitOfCompactSubgroups` restricts the ambient
compact-limit premise using closedness of the actual Levi.
`continuous_standardLeviProjection` compares the ambient decomposition
from `StandardCocharacterStatement` with the literal restricted
decomposition from `StandardLeviIntersectionStatement`. It derives the
required continuity even though those decompositions were constructed
separately.

The representation-theoretic dependencies are only the definitions of
the named compact-subgroup condition and of semidirect decompositions.
The proof uses no classification, character independence, geometric
lemma, adjointness, cuspidal-support theorem, or Aubert Proposition 3.2.

The local instance `restrictedLeviPointTopology` uses the canonical
`pointTopology` on rational points. Its explicit name allows this module to be
imported together with the rational alternating-operator modules.
