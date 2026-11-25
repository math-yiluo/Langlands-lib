# Downstairs integral tori and fixed-torus parabolic attainment

This internal supporting module for the parabolic order problem constructs an
actual split integral apartment torus in each supplied apartment-point model.
It proves attainment, over the original residue field, of every parabolic
containing that torus in the reductive quotient. All results are at arbitrary
universe `u` and all image equalities concern subgroup functors on every scheme
test.

`HasResidueFixedTorusQuotientAttainment` quantifies over a generic factorization
of the base-changed downstairs apartment torus through the upstairs apartment
torus, an apartment point `x`, and a supplied reductive special-fibre quotient
of the actual family model at `x`. Its conclusion constructs `T` satisfying
the full integral torus clause, proves that its quotient inclusion is maximal
split, and attains every supplied parabolic inclusion through which that
quotient torus inclusion factors. The source is an actual incident downstairs
facet, and the morphism is the supplied family morphism.

The proving theorem `hasResidueFixedTorusQuotientAttainment` assumes the
apartment axioms and common apartments downstairs, an equivariant building
map, an affine apartment map compatible with it and with exact facet
restriction, and the all-facet unramified zero-fixer characterization of the
supplied model family. It also assumes that the character-valuation kernel
of the base-changed downstairs torus fixes the image of the downstairs
apartment pointwise. The generic torus factorization remains explicit in the
proposition; this module does not construct it.

The implemented proof has the following steps.

1. `IsParabolicSubgroup.exists_cocharacter_of_maximalSplitTorus` works over an
   arbitrary field. Given a connected reductive group, a prescribed maximal
   split torus and a parabolic containing it, the published `parabolicDynamic`
   theorem supplies an ambient cocharacter. Its range factors through the
   parabolic. Smooth connected split-torus conjugacy inside that parabolic
   conjugates the cocharacter into the prescribed torus. The conjugating point
   belongs to the parabolic, so conjugation preserves that subgroup functor.
   This identifies the original parabolic with the dynamic parabolic of a
   cocharacter of the same prescribed torus. No ambient splitness is assumed.
2. `IntegralTorusData.isMaximalSplitTorus_quotient` applies the published
   maximal-split-torus transfer theorem to the represented smooth connected
   unipotent radical over a perfect residue field. It keeps the original torus
   and its actual composite inclusion into the quotient.
3. `exists_integralTorus_at_apartmentPoint` applies `unramifiedTorusClause`
   with conjugating point `1` and the upstairs singleton `{a x}`. The given
   fixedness supplies its torus-fixedness premise; the all-facet
   characterization supplies the singleton model equality. The constructed
   torus lies in the actual supplied downstairs model and satisfies both
   closed splitness and maximal split special-fibre conditions.
4. `exists_incidentFacet_quotientImage_eq_parabolic_of_torus` applies step 1
   to the quotient torus from step 2. The inverse canonical cocharacter
   specialization lifts the resulting residue torus cocharacter to the
   downstairs generic torus. The published
   `exists_incidentFacet_quotientImage_eq_residueCocharacter` then supplies the
   actual incident facet and the exact schematic quotient-image equality.
   The specialization inverse identity identifies that image with the
   prescribed parabolic. The final theorem packages these constructions.

The two local coefficient instances in `UnramifiedTorusClause` have explicit
module-specific names. This avoids a generated declaration-name collision
with `UnramifiedFacetImageOrderDescent`, permitting their joint import.

The provenance is internal: the proof composes the published rational dynamic
classification, smooth split-torus conjugacy, unipotent quotient transfer,
integral torus clause and residue cocharacter attainment. It makes no new
translation claim about original literature. It does not assert attainment
of parabolics lacking the specified torus containment, unconditional image
parabolicity, or the full facet order bijection.
