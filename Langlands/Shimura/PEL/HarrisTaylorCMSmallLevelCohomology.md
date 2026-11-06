# Shrinking-level cohomology of the actual geometric CM tower

This internal construction specializes the published restricted-level colimit
and cohomology APIs to the existing geometric CM scheme tower. It retains the
chosen representation of the exact CM moduli presheaf and its actual change
of base to the algebraic closure of F. No external-literature assertion is
introduced.

The adapter identifies the ordered small-level category and its inclusion and
forgetful functors with `CompactOpenLevel.RestrictedOrdered`,
`restrictedInclusion`, and `restrictedForget`. These are definitional
equalities. The two actual smallness instances use the published inheritance
under subgroup containment and the published conjugation lemma. Finite
dimensionality over the rationals is required by these instances. In the CM
specialization it is derived from the finite-dimensional F-algebra in D and
the number-field tower, rather than assumed independently.

All CM fields, compatible algebra structures, the Harris signature charts,
tensor comparison and coherence propositions, Picard propositions, duality
naturality, polarization stability, Weil-transition compatibility, adelic
comparison and torsion-etaleness input are retained. The parameter q is the
existing `CMRepresentabilityStatement` for these exact inputs; the underlying
scheme tower is exactly `cmGeometricSchemeTower ... q`.

`cmGeometricSchemeTower_restrictedSelfArrow` applies the existing geometric
coset-map identity to the generic restricted self-arrow. It proves that an
element of a small level fixes that same geometric scheme. It does not prove
an identity on a general coefficient sheaf.

For the cohomological constructions, dual-scheme existence and geometry,
geometric coarse rigidity at every small level, and the named dominant
unramified-to-etale criterion remain explicit. `cmSmallLevelTowerEtale`
packages the proved etaleness of every actual arrow using
`cmGeometricSchemeTower_map_etale_of_dominantCriterion`. An arbitrary scheme tower or an assumption
that all of its arrows are etale is not substituted for this construction.
All scheme and coefficient-ring universes in this specialization are zero.

`cmSmallLevelCoefficientDiagram` abbreviates an actual `CoefficientDiagram`
on the opposite of this geometric tower, with the proved etaleness
installed in its definition. `cmSmallLevelTrivialCoefficients` is precisely
the published sheaf-level triviality property on these diagrams. A
coefficient diagram has small-etale module sheaves as its objects, and its
transition morphisms satisfy the published identity and composition laws
at the sheaf level. `cmSmallLevelCohomology` abbreviates the resulting
degreewise cohomology functor with the same proved etaleness instance. `cmSmallLevelCohomologyDiagram` restricts the
resulting degree-d cohomology functor to the actual ordered small-level
inclusions. Its equality to the generic restricted diagram is definitional.
`cmSmallLevelColimitCohomology` equips this colimit with the published action
of the opposite finite-adelic group of the rational involution in D.

`cmSmallLevelSmoothCohomology` and
`cmSmallLevelSmoothCohomologyFunctor` use the additional explicit
`cmSmallLevelTrivialCoefficients` premise, which is the published
`IsLevelTrivialCoefficients` premise for this actual tower. This premise
requires both equality of the self-arrow's scheme map with the identity-arrow's scheme map and
the corresponding identity for its coefficient morphism after restriction
is identified along that equality. Smoothness is supplied by the published
restricted cohomology theorem. The functor acts on the full subcategory of
coefficient diagrams satisfying that same premise.

`cmSmallLevelSmoothCohomology_action` identifies translation of a class
represented at U with pullback through the actual geometric transporter
from g U g-inverse to U, together with its supplied coefficient morphism,
followed by the colimit inclusion at that conjugate level. This is the
published action formula applied to this exact tower.
`cmSmallLevelCohomology_exists_level_class` applies the generic single-level
representative theorem after installing actual downward closure. It retains
an explicit `Nonempty (SmallCMLevel D)` premise. The colimit's indexing
category is the opposite ordered category, so its maps shrink the levels.

This unit constructs the cohomology colimit conditionally. It does not prove
q, arithmetic existence, small-level existence, the named geometric inputs,
or coefficient-level triviality of a general nonconstant Harris coefficient
system. In particular, the scheme self-arrow identity alone is not used to
infer the coefficient premise. It does not extend the actual tower to levels
that are not sufficiently small, or introduce canonical-model or Galois
machinery.
