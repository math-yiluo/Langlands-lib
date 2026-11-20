# The two actual CM places of a split finite center

`SplitPlaceIdentification.placesEquivFinTwo` identifies the actual places of
the CM field above \(p\) with the two factors of a supplied split center. The
published completed tensor comparison expresses that center as the product of
the actual completed fields above \(p\). The supplied split-center chart also
expresses it as two copies of the real-field completion. Taking the prime
spectrum identifies the two index types, since the spectrum of a finite product
is the disjoint union of the spectra of its factors and each field has a
singleton spectrum.

`card_finitePlacesAbove_of_isSplitPlace` gives the resulting count under the
existence predicate `IsSplitPlace`. Thus `IsDivisionAbove` at the prescribed
split place in `ClozelOnePlaceExistenceStatement` requires division at exactly
two places. This is an internal consequence of the published finite completed
tensor comparison and Mathlib's spectrum of a finite product.
