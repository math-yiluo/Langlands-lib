# Compact-chart regularity of actual translated comparisons

The compact chart `unitaryChart` identifies the unitary coefficient fiber of a
parabolic presentation with its fixed compact tensor carrier.

`ofCommonLevi_locallyFinite` first reindexes the target-side common-Levi family
along the continuous unitary conjugation map. Its chart value is locally finite.
The translated comparison precomposes this family with the unitary translation,
whose value in the fixed charts is independent of the parameter. Local
finiteness follows by composing the two chart values.

`actualComparison_locallyFinite` applies this result to the continuation in the
certificate `IsActualComparison`. The regular unitary extension of that
continuation gives local finiteness via
`isLocallyFinite_of_regularUnitaryExtension`. The equality in the certificate
identifies the translated continuation with the given comparison.

`actualComparison_coefficientMap` and `actualComparison_bijective` extract
the coefficient identity and pointwise bijectivity on the translated fibers
from the same certificate.

This is the compact-chart regularity used to extend the coefficient comparison
equations over the unitary family in Waldspurger, *La formule de Plancherel pour
les groupes p-adiques (d'après Harish-Chandra)* (2003), V.3.2, printed p. 295,
PDF p. 61. The argument uses the Library's actual translations and local
regular representatives of standard-operator continuations.
