# Common apartments from the polysimplicial building axiom

This internal construction fixes the existing quotient and action of supplied
`B : ValuationBuildingData G`, at every universe `u`, and a supplied
`R : B.PolysimplicialRealization`. Its retained geometric premise is
`AbstractBuilding.IsBuilding R.complex R.apartments`, the `isBuilding` clause
of `B.SatisfiesBuildingAxiom R`.

`exists_buildingFacet_mem` first proves that every actual point lies in an
existing building facet. Represent the point as `g • B.apartmentMap a`.
The translate of the affine-root facet containing `a` is such a facet, and
contains the represented point by the definition of that facet.

`PolysimplicialRealization.exists_isApartment_mem_mem` then proves common
apartments for any two actual points. Choose facets containing them and use
`R.realize.symm` to obtain facets of the abstract polysimplicial complex.
The thick chamber-complex clause extends each facet to a chamber. The
building axiom puts both chambers in one abstract apartment, and its
subcomplex clause puts both original abstract facets there too.
Unpacking `R.apartments` identifies this abstract apartment with
`R.apartmentComplex Y` for an actual translated apartment `Y` in the existing
quotient. The definition of `apartmentComplex` says that the realizations of
both facets lie in `Y`. Hence both original points lie in `Y`.

`PolysimplicialRealization.commonApartment` chooses one such actual subset
`Y`; `commonApartment_spec` proves that it is an apartment and contains both
specified points. The choice uses precisely the existence proof just
described. No common-apartment predicate is supplied as an additional
premise. `hasCommonApartmentWith_of_isBuilding` packages the result in the
existing `B.HasCommonApartmentWith` predicate.

The final `eq_of_compactStabilizer_fixed_of_isBuilding` applies the published
apartment-to-global fixed-point reduction to these common apartments. It
retains topology compatibility and the apartment singleton fixed-locus
premise for the actual subgroup
`B.compactStabilizer (B.apartmentMap x)`. Under those premises, every point
of the existing quotient fixed by that subgroup equals `B.apartmentMap x`.
No extra apartment-transitivity premise is needed, since the published
reduction already derives the necessary sharp-fixer transitivity from the
quotient relation.

The provenance is internal: these deductions unpack the published
`AbstractBuilding.IsBuilding`, `PolysimplicialRealization.apartments`,
`apartmentComplex` and the existing quotient facet definitions, and apply
the published `ApartmentFixedPointReduction` theorem. No external source
assertion is introduced. Worker 1483 contributed the apartment-to-global
reduction used here; Worker 1681 implemented the common-apartment
construction and its deductions.

This construction discharges the separate common-apartment premise once the
displayed building axiom has been established for actual supplied data.
It supplies no building data or building-axiom witness, metric, canonical
integral model, supplied-model comparison, special point or apartment
singleton fixed locus. Those obligations remain in the unchanged
`IntegralModel.BuildingComparisonStatement` construction.
