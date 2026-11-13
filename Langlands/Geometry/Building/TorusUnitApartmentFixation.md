# Torus units fix the apartment through a source factorization

`TorusUnitApartmentFixationStatement` is an internal elementary consequence
of the existing full V6 compatibility predicate. It allows any field with
an integer-valued valuation, actual apartment data and centralizer, and
any group-scheme source mapping into the apartment torus. Every source
point in its character-valuation kernel fixes the building image of
every apartment point. The source need not itself be a torus.

`torusUnitApartmentFixation` proves the statement. Map a source unit into
the actual centralizer through the torus factorization. Functoriality
of `characterValuationKernel` puts its image in the centralizer kernel.
The published theorem
`IntegerValuation.IsOmegaCompatible.map_mem_reducedFixer` says that this
image fixes the apartment point in the reduced building. The centralizer
factorization equation identifies its image in the acting group with the
original source point's image.

`isFixedByScalarTorusUnits_apartmentMap` applies that proof after scalar
extension along an arbitrary extension of fields in the same universe.
The existing `IsFixedByScalarTorusUnits` predicate then records fixation
through the composite of the source map and the torus inclusion.
The centralizer datum and V6 compatibility belong to the extended
apartment, and base change preserves the composite.

This module proves only the unit fixation of an already supplied
apartment point. It does not place a prescribed coefficient-fixed
building point in a special apartment or prove the unramified covering
theorem. Its provenance is internal: both proofs use existing
character-kernel functoriality, the centralizer factorization, V6
fixation, and functoriality of base change.
