# Equivariant descent through actual finite cover refinements

Author: Worker 56.

This internal construction proves refinement invariance of equivariant
continuous gluing for actual finite full-domain covers. It explicitly
constructs an open subgroup preserving both covers. The two covers'
individual maximal stabilizers need not coincide.

## Fixed subgroup and continuous gluing

Let `K : Type u` be a complete ultrametric normed field, let `P` be a
presented positive-polyradius affinoid quotient, and let `G : Type v`
be a topological group with a supplied `DomainSpectralAction G P`.
Fix an open subgroup `H`, an `H`-invariant represented domain `d`,
an actual finite cover `c` of `d.obj`, and a witness
`hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)`.
The target `Y : Action TopCat.{w} H` has an independent universe.

`InvariantCoverFamily` contains equivariant continuous maps from the
unchanged component loci to `Y`, agreeing whenever their arguments
have the same ambient spectrum point. Each source action restricts
the original ambient inverse-pullback action to its component locus.
`invariantCoverEquivariant_iff` detects equivariance of a continuous
map on the target locus on these components: coverage supplies a
component containing any target point, and its equivariance equation
is the same equation on that ambient point.

`invariantCoverRestrict` uses the original cover inclusions.
`invariantCoverGlue` uses exactly `c.glue`, the continuous quotient lift
from the actual finite disjoint union of component section spectra.
Its equivariance follows from the component restriction identities and
the detection theorem. The two inverse laws give
`invariantCoverGluingEquiv`.
At `ρ.finiteFamilyOpenSubgroup H c.obj`, this equivalence is
definitionally the previous `finiteCoverGluingEquiv`, as exposed by
`invariantCoverGluingEquiv_finiteFamily`.

`invariantCoverFamilySubgroup` restricts every component to a smaller
open subgroup through the published continuous subgroup inclusion,
leaving the compatible continuous maps unchanged. The restriction
and gluing comparisons show that these operations commute with
changing subgroup. In particular, subgroup restriction preserves
the exact original quotient lift.

## Actual refinement restriction

Let `b` be another finite cover of `d.obj`, invariant under the same
subgroup, and let `r : Domain.FiniteCover.Refinement b c`. Every finer
component has its selected coarser index `r.index j` and an actual
bounded domain arrow `r.map j`. The forward map
`invariantCoverRefinementPullback` has continuous component

```text
(g (r.index j)).comp (r.map j).locusMap.
```

The two source actions and the inclusion preserve the same ambient
point, so the original coarser equivariance equation proves the finer
one. The published nonequivariant `compatible_pullbackFamily` proves
compatibility. The application lemma exposes this exact formula.

Refining the component restrictions of a global equivariant map
gives its finer restrictions. The theorem
`invariantCoverGlue_refinement` identifies the finer glued map with
the original coarser glued map. Its proof applies the published
continuous-map refinement theorem to the unchanged underlying maps.

`invariantCoverRefinementEquiv` uses this actual refinement pullback
as its forward map. Its inverse glues the finer family and restricts
it to the coarser cover. Refinement invariance and the gluing inverse
laws prove both inverse identities. No individual refinement arrow
is required to be surjective, and the index function need not select
every coarser component.
`invariantCoverRefinementPullback_eq` proves that different actual
refinement choices act identically on compatible equivariant families.
Both give the same glued map, so injectivity of the finer gluing
equivalence proves equality. Their index functions remain distinct data.

## Constructed common subgroup

For any two supplied covers `c` and `b`, `commonCoverOpenSubgroup` is
the intersection

```text
ρ.finiteFamilyOpenSubgroup H c.obj ⊓
ρ.finiteFamilyOpenSubgroup H b.obj.
```

Its membership theorem says precisely that a group element belongs
to `H` and preserves every locus in both original covers. It is
contained in both covers' individual common open subgroups and in
`H`. The two stabilizer lemmas prove preservation of each component.
Thus an `H`-invariant target and both covers can be restricted to
this actual open subgroup.

The entry construction `commonCoverRefinementEquiv` applies the fixed
subgroup descent equivalence there. It retains every original
representation, target map, chosen refinement index and actual
bounded refinement arrow. Its target is any supplied action of this
common subgroup. A target action of either larger subgroup can be
restricted by `Action.res` along the constructed continuous inclusion;
the preceding subgroup comparisons apply to the corresponding families.

## Provenance and limits

This unit derives from `DomainEquivariantGluing`,
`DomainEquivariantSubgroupRestriction`, `DomainCoverDescent` and the
finite common-stabilizer construction. It claims no additional
literature theorem. The proof concerns the actual continuous maps
on represented loci and the actual bounded maps stored in supplied
refinements. It does not infer equality of algebra maps from their
values on spectrum points.

Empty covers and loci, nilpotents, zero quotients and trivial scalar
valuations remain allowed. The action category supplies continuous
fixed-element operators. Joint continuity in the group parameter,
algebra-section descent, intersections, analytic structure sheaves,
analytic atlases, analytic etale sites and Harris specialization remain
further work.

The subgroup inclusion used here is the published
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.openSubgroupInclusion`,
reused through `DomainInvariantSubgroupRestriction`.
