# The compact-restriction inertia decomposition from Renard VI.3.2(ii),(iii)

This module is an internal reduction for the proof of
`Langlands.CuspidalSupport.RationalCompactRestrictionInertiaDecompositionStatement`.
It does not prove that statement on its own. Its last theorem derives it from
two published propositions that are taken as hypotheses. These are Renard
VI.3.2(ii) (`RationalNormKernelFiniteRestrictionStatement`) and VI.3.2(iii)
(`RationalNormKernelTwistEquivalenceStatement`). Neither proposition is proved
here, and neither is a premise of the final target. The final proof will apply
this theorem to their independently published proofs. The module has two
generic layers, for an open subgroup and for an open normal subgroup, followed
by the rational application.

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

## The rational application

`rationalCompactRestrictionInertiaDecomposition_of_normKernel` assumes
`hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}` and
`htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV}`. It concludes
`RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV}`, the
unchanged target.

The proof introduces the field, the connected reductive group scheme and the
target's instances, and puts the canonical topology `rationalPointTopology F G.X`
on the rational points. It then introduces the irreducible `π` and the target's
compact-coefficient premise for the restriction of `π` to
`N := Plancherel.rationalCommonNormKernel G`. `N` is open by the published
`Plancherel.isOpen_rationalCommonNormKernel` and normal by the published
instance. The finite irreducible spanning family of the restriction comes from
the last conjunct of `hfin` applied to `π`. The semisimplicity and
finite-length conjuncts are not used.

The target's factors `rationalInertiaDecompositionProperties G π` are equal to
`SmoothRep.irreducibleSubquotientProperties (IsRationalInertiaRelated G π)`. Both
Bool cases hold by `rfl`: the `true` factor is `rationalInertiaBlockProperty G π`
and the `false` factor is `rationalInertiaComplementProperty G π`. So it
suffices to apply `openNormalFamily_categoryDecomposition` with
`P := IsRationalInertiaRelated G π`.

The remaining test compares restrictions with inertia. Fix an irreducible `D`.
`htw` applied to `D` and `π` gives `(A ↔ B) ∧ (A ↔ C)`. Here `A` says that the
restrictions of `D` and `π` to `N` are equivalent, `B` says that
`Langlands.twist χ D ≃ π` for some `χ` in the published unramified-character
subgroup, and `C` says that a nonzero intertwiner maps the restriction of `D`
into the restriction of `π`. Hence `C ↔ B`. It remains to identify `B` with
`IsRationalInertiaRelated G π D`, that is, with `∃ χ, D ≅ rationalUnramifiedTwist G χ π`:

- From `B`: the equivalence `twist χ D ≃ π` is an isomorphism
  `rationalUnramifiedTwist G χ D ≅ π` (`SmoothRep.mkIso`). Its inverse shows
  `IsRationalInertiaRelated G D π`, and the published
  `IsRationalInertiaRelated.symm` (inverse character) gives
  `IsRationalInertiaRelated G π D`.
- Conversely, `IsRationalInertiaRelated.symm` yields `χ` and
  `π ≅ rationalUnramifiedTwist G χ D`. The inverse isomorphism, converted by
  `SmoothRep.equivOfIso`, is an equivalence `twist χ D ≃ π`.

The representation underlying `rationalUnramifiedTwist G χ D` is
definitionally `Langlands.twist χ.val.toMonoidHom D.representation`, so these
conversions involve no twist-direction change beyond the explicit use of
`symm`.

## Provenance and scope

All declarations are internal compositions of published Library results:
the compact open basis, the IV.1.4–IV.1.5 compact splitting, compact coefficients of
subrepresentations, the finite-family ambient projector and its irreducible
test, the natural-idempotent category decomposition, and the rational inertia
API. Their mathematical route follows Renard VI.3.3.1, which constructs the
inertia block from the finitely many restriction types given by VI.3.2(ii)
with the IV.1.5 projectors and identifies it with the inertia class by
VI.3.2(iii). No step of the source proof of VI.3.2 is reproved here. The
module adds no axioms. Its declarations depend only on `propext`,
`Classical.choice` and `Quot.sound`.
