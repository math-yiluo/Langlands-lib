# Building data over the actual maximal unramified field

Worker 60 defines `MaximalUnramified.BuildingData F G` as the abbreviation
`IntegerValuationBuildingData (MaximalUnramified.valuation F) G`, where `G`
is an affine group scheme over the actual field
`LocalGalois.Separable.inertiaFixedField F`. The base field `F : Type u`
has the existing nonarchimedean local-field structures, in arbitrary universe
and characteristic. This definition requires no
`IsNonarchimedeanLocalField` instance on the inertia fixed field.

The integer-valued valuation is constructed in
`MaximalUnramifiedValuation` from the published induced valuation, the
intrinsic base-to-fixed-field value-group isomorphism, and the base integer
normalization. That module proves surjectivity, exact restriction to
`FML.normalizedMultiplicativeValuation F`, equality of valuation rings
under inclusion into the same fixed field, and equality of source-positive
orders on base units. Here `order_base_eq_localFieldOrder` also identifies
the real order on base units with `Building.localFieldOrder F`, by combining
the proved real restriction with the generic local normalization equality.
The order is positive in the corrected KP convention; apartment translation
is its negative through the centralizer adapter.

This is a specialization of the generic supplied-data type. An element still
supplies connected reductivity of `G`, a maximal split torus, its actual
`KPApartmentData` equipollence class, the representing `CentralizerDatum`
including restriction-evaluation bijectivity, and full V6 on that same class.
The inherited apartment, reduced quotient, root filtrations, rational-point
action, apartment map and fixers are those of that supplied class.
Its one-group stabilizer remains exactly the character-valuation kernel
intersected with the reduced fixer, with the generic centralizer-kernel
inclusion. The abbreviation introduces no second quotient or additional
building data and asserts no inhabitance.

The original motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Chapter 7 opening (printed pp. 235–236 / PDF pp. 266–267)
and Chapter 8 opening (PDF p. 314), where the maximal unramified field and
its integer ring are used. Notation 2.6.15 (printed pp. 102–103 /
PDF pp. 133–134), with the authors' 1 November 2024 corrections, PDF p. 25,
fixes the positive character-valuation convention. The correction at PDF
p. 33 adds AS5 to the Chapter 7 construction hypotheses. This derived
specialization uses the already constructed arithmetic adapter and generic
data type; it proves no AS5, V7, building existence, compactness, parahoric
identification, integral-model existence or unramified descent.
