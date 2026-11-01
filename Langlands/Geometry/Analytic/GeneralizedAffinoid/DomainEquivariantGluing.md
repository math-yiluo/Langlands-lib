# Equivariant continuous gluing on finite represented-domain covers

Worker 56 constructs the equivariant refinement of the published
`Domain.FiniteCover.glue`. The construction retains its continuous
quotient lift and the original represented domains and bounded cover
arrows. This is internal derived content.

## Inputs and equivariant maps

The scalar field `K : Type u` is complete, normed and ultrametric.
`P : PresentedAffinoidAlgebra K` is an actual finite positive-polyradius
closed Tate quotient. Fix a topological group `G : Type v`, a supplied
`ρ : DomainSpectralAction G P`, an open subgroup `H`, an invariant
represented domain `d`, and an actual finite cover `c` of `d.obj`.
The cover retains its component full representations, actual bounded
restriction maps and pointwise coverage of the target locus.

The common open subgroup is the previously constructed
`J = ρ.finiteFamilyOpenSubgroup H c.obj`. It preserves every component
locus and the target locus, with their original representations.
The target `Y : Action TopCat.{w} J` has a universe independent of
both the field and the acting group.

`LocusEquivariant` is the proposition that a continuous map `f` obeys
the pointwise equivariance equation for every group element and every
point of its source locus. The source operator is the previously
constructed restricted ambient inverse-pullback operator. The target
operator is the supplied continuous endomorphism `Y.ρ g`.
`EquivariantLocusMap` is the subtype of continuous maps obeying that
equation.

When the target has universe `u`, `equivariantLocusMapHomEquiv`
identifies this subtype with the ordinary morphisms from the actual
`invariantLocusAction` to `Y` in Mathlib's action category. The two
directions keep the same continuous map and convert between the
pointwise equation and equality of continuous composites.

## Descent construction and inverse laws

`finiteCoverLocusInclusion` is the equivariant inclusion induced by
each original bounded cover arrow. Its underlying map is exactly
`(c.map i).locusMap`; thus it preserves the ambient spectrum point.

`finiteCoverEquivariant_iff` proves that equivariance of a continuous
map on the target locus is equivalent to equivariance of every
component restriction. In the forward direction the restricted
source actions and inclusions commute. In the reverse direction,
the covering property places each target point in a component.
The component equation is then the same equation on that ambient
point. No nonemptiness or positive cover size is required.

`FiniteCoverEquivariantFamily` contains equivariant continuous maps
on all component loci, with the published compatibility condition:
maps agree whenever their arguments have the same underlying point
in `BanachSpectrum P`. `finiteCoverRestrict` composes with the
unchanged locus inclusions. Its compatibility follows from
`c.compatible_restrict`, and equivariance follows from the detection
theorem.

`finiteCoverGlue` uses the published `c.glue` on the underlying
compatible continuous maps. This assembles maps on the actual finite
disjoint union of component section spectra and descends through
`c.totalMap`, whose quotient property uses the actual target subspace
topology. The component restriction identities then prove
equivariance. Equivariance of the glued map is a conclusion, rather
than a supplied hypothesis.

`finiteCoverGlue_apply_spectrum` gives its value on every component
spectrum. `finiteCoverRestrict_glue` and `finiteCoverGlue_restrict`
are the two inverse laws. `finiteCoverGluingEquiv` packages them as
an equivalence between equivariant maps on the target locus and
compatible equivariant component families. `finiteCoverGlue_unique`
proves uniqueness from the component restriction identities.

## Target naturality and categorical form

For an ordinary equivariant morphism `p : Y ⟶ Z` of targets in
universe `w`, `equivariantLocusMapPostcomp` and
`finiteCoverFamilyPostcomp` postcompose the global map and every
component map, respectively. The commutativity equation of `p`
proves equivariance, and equality is preserved on all overlaps.
`finiteCoverRestrict_postcomp` and `finiteCoverGlue_postcomp` prove
that restriction and quotient-lift gluing commute with these maps.
The latter uses the published continuous-map gluing naturality.

When the target has universe `u`,
`FiniteCoverCompatibleHomFamily` uses ordinary action-category
morphisms on each component. `finiteCoverHomFamilyEquiv` identifies
these families with the independent-universe formulation.
`finiteCoverHomGluingEquiv` is the resulting equivalence between
actual equivariant morphisms on the target locus and compatible
component morphisms. Its forward component is composition with
`finiteCoverLocusInclusion`. Its inverse has exactly the original
continuous quotient lift `c.glue` as underlying map.

## Provenance and limits

This unit derives from `DomainGluing`, `DomainFiniteInvariantCover`
and `DomainInvariantLocus`, together with Mathlib's definition of
`Action.Hom`. It attributes no additional literature theorem.
The proofs use pointwise covering and the already constructed
continuous quotient lift. They do not infer equality of bounded
algebra maps from equality on spectrum points.

The empty-cover case is retained: coverage then forces an empty
target locus. No point of the topological target is selected.
Nilpotents, zero quotients and trivial scalar valuations remain
allowed. `Action TopCat J` supplies continuous fixed-element
operators; joint continuity in the group parameter remains a
separate obligation. The construction concerns continuous maps
between represented loci. Gluing algebra sections, analytic
atlases, structure sheaves, analytic etale sites and the Harris
specialization remain further work.
