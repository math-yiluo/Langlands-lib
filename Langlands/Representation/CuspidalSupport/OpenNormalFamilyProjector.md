# Finite-family projectors for an open normal subgroup

This internal module contains the generic open-subgroup and open-normal-family
constructions originally proved by Worker 1168 in
`RationalCompactRestrictionInertiaReduction`. Worker 1740 extracted them without
changing any declaration name, namespace, universe binder, signature or proof.
The module has no rational inertia statement imports and can be used with the
actual compact-induction constructions independently of the rational reduction.

## Open subgroups

The group `G` is a locally compact nonarchimedean topological group, and `N` is
an open subgroup with its inherited topology.

- `openSubgroup_compactOpenCofinal`: every open subgroup `K` of `N` contains a
  compact open subgroup of `N`. The image of `K` in `G` is open because `N` is
  open. The published compact open neighbourhood basis
  `compactOpenSubgroupBasis` gives a compact open subgroup `V` of `G` inside
  this image, so `V` lies in `N`. Its preimage in `N` is open, contained in
  `K`, and compact, since its image in `G` is `V`.
- `openSubgroup_isCompl_isotypic_annihilator`: for every compact-coefficient
  class `c` of `N` and every smooth complex representation `X` of `N`, the
  intrinsic isotypic subrepresentation of `c` in `X` and its annihilator
  subrepresentation are complementary. `N` is locally compact because it is
  open. The proof equips `N` with its Borel σ-algebra and its Haar measure.
  It then applies the published splitting
  `CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation`
  (the splitting of Renard IV.1.4, realized by the projectors of IV.1.5)
  with the cofinality lemma above.

## A finite irreducible family on an open normal subgroup

Now `N` is moreover normal. Fix a smooth complex representation `π` of `G`
whose restriction to `N` has compact smooth-dual coefficients (`hc`). Fix also
a finite family `W : Fin m → Subrepresentation (π.representation.comp N.subtype)`
of irreducible subrepresentations (`hWirr`) whose sum is the whole restriction
(`hWspan`). These data are explicit parameters of the declarations below, not
assumptions about `π` beyond what is stated.

- `openNormalFamilyObject i` is the subrepresentation `W i`, viewed as an
  irreducible compact-coefficient smooth representation of `N`. It is smooth
  because a subrepresentation of a smooth action is smooth. It has compact
  coefficients by the published
  `hasCompactSmoothDualCoefficients_subrepresentation` applied to `hc`.
- `openNormalFamilyInclusion i` is the inclusion of `W i` into the restriction
  of `π`, as an intertwiner. It is injective
  (`openNormalFamilyInclusion_injective`), and the ranges of all inclusions
  span the restriction (`openNormalFamilyInclusion_span`, which is `hWspan`).
- `openNormalFamilyProjector X` is, for every smooth `G`-representation `X` in
  any carrier universe, the published finite-family ambient projector
  `CompactCoefficientClass.finiteFamilyAmbientProjector`. That projector
  belongs to the classes of this family and has ambient object `π`. Its
  complement hypotheses for `π` and for `X` are discharged by
  `openSubgroup_isCompl_isotypic_annihilator`. Conjugation stability of the
  selected classes comes from the finite spanning family through the published
  construction, so the convention σ^g(h) = σ(g⁻¹hg) is inherited from it.
- `openNormalFamilyProjector_idempotent` and `openNormalFamilyProjector_natural`
  restate the published idempotence and naturality, the latter for every
  ambient intertwiner between objects in independent carrier universes.
- `openNormalFamilyProjector_fixes_iff`: on an irreducible `X`, the projector
  acts as the identity if and only if some nonzero intertwiner maps the
  restriction of `X` to `N` into the restriction of `π`. This is the
  published `finiteFamilyAmbientProjector_fixes_iff_restricted_hom`.
- `openNormalFamily_categoryDecomposition`: let `P` be an object property of
  smooth `G`-representations in the carrier universe of `π`. Suppose that, for
  every irreducible `D`, `P D` holds exactly when a nonzero intertwiner maps
  the restriction of `D` into the restriction of `π`. Then the Bool-indexed
  all/no irreducible-subquotient properties of `P`
  (`SmoothRep.irreducibleSubquotientProperties P`) form a
  `Renard.IsCategoryDecomposition`. The proof applies the published
  `SmoothRep.categoryDecomposition_of_natural_idempotent` to the projector,
  using its naturality and idempotence, with `openNormalFamilyProjector_fixes_iff`
  composed with the hypothesis on `P` as the irreducible test. The decomposition
  therefore has actual coproducts of the all- and no-subquotient factors for
  every object, including objects of infinite length, and vanishing
  off-diagonal morphisms in both directions.

## Provenance and scope

These are derived compositions of the published compact open basis, the
IV.1.4–IV.1.5 compact splitting, compact coefficients of subrepresentations,
the finite-family ambient projector and its irreducible test, and the natural
idempotent category decomposition. Their use in Renard VI.3.3.1 is explained in
[RationalCompactRestrictionInertiaReduction](RationalCompactRestrictionInertiaReduction.md).
The finite irreducible spanning family and compact coefficients of the whole
restriction are explicit inputs. This module proves no rational finite-restriction,
twist-equivalence, or small-progenerator statement and adds no axioms.
