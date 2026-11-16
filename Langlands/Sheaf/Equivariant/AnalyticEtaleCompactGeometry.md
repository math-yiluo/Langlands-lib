# Geometric inputs to compact analytic étale sections

Author: Worker 627.

This module connects the published support and compact-section
constructions to the geometric hypotheses of the analytic compact comparison.
It is an internal deduction from the Library constructions and proofs.
The geometric inputs are discharged by the published theorems
`etaleOpenDomainStatement` and `etaleOpenMap`; neither is an additional premise.

The base field `K` is a complete ultrametric normed field, `L` is a normed field
with a normed `K`-algebra structure, and `X` belongs to
`LocalizedCategory.{u,v,v}`. The supplied family `h` consists of the
`EtaleSite.PointAxioms` for all `L`-valued points of `X`. Every declaration
assumes that the underlying space of `X` is Hausdorff.

`etalePointLifting_of_hausdorff` applies the published conditional lifting
theorem to `etaleOpenDomainStatement X`. The imported lifting argument uses
the open complement of an underlying point and the point axioms. This adapter
requires no surjectivity of the point projection.
`support_etaleSelf_eq_preimage_of_hausdorff` then applies the existing support
descent theorem: the field-valued support of a global section is the full
preimage of its image under `pointProjection`.

With surjectivity of that projection, the next two theorems show closedness
of the actual underlying support and identify compact support in field-valued
points with compactness of that actual support. They instantiate the existing
support-descent results with the preceding lifting theorem and
`etaleOpenMap K U.hom U.prop` for each ordinary étale object `U`. Their
statements concern any module presheaf and its global sections. Compact support
upstairs uses the existing topology induced by `pointProjection`.

For a topological group `G` in any universe and `ρ : G →* Aut X`,
`isIso_etaleCompactInclusion_of_hausdorff` instantiates the published
`isIso_etaleCompactInclusion` with the same lifting and openness results.
The coefficient ring has the original universe `max u (v + 1) uL`.
The resulting natural isomorphism `etaleCompactSectionsIsoOfHausdorff` compares

```lean
etaleGSheafCompactSections L ρ h R ⋙ smoothForget R G
```

with

```lean
etaleGSheafRestriction ρ R ⋙ etaleCompactSections L h R.
```

It is `asIso` of the existing `etaleCompactInclusion`; the final theorem
identifies its forward transformation with that canonical inclusion by
reflexivity. These degree-zero declarations require surjectivity, but no
compactness of the whole space, continuity of the whole action, smallness
of `G`, or admissible-refinement hypothesis. The module supplies the
support and degree-zero inputs to the comparison; higher-degree comparison
and compact acyclicity remain separate obligations.
