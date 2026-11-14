# A common apartment and its integral split torus in a pair-fixer model

This internal construction assembles published common-apartment and split-torus
closure results. It applies to the actual maximal-unramified quotient attached
to a supplied `MaximalUnramified.BuildingData F G`, with no local-field
assumption on the maximal unramified field.

`PairApartmentTorusData B N y₁ y₂` records a rational point `q`, two actual
apartment coordinates with `q • apartmentMap xᵢ = yᵢ`, and a closed integral
split torus in the supplied integral model `N`. Its generic torus is identified
with the supplied apartment torus and its generic inclusion is exactly the
supplied inclusion followed by the inner automorphism of `q`.
The compatibility is the `generic_comm` field of `IntegralSplitTorusData`;
it is a scheme-morphism equality.

`unramifiedPairApartmentTorusData` chooses these data whenever the
character-valuation kernel intersected with the pair's pointwise fixer is
contained in `N.integralPoints`. The model need not have connected or reductive
special fibre. The endpoints need not be distinct or coefficient-fixed.
The construction works at arbitrary universe `u` and in both characteristics.

The implemented proof uses:

* `MaximalUnramified.commonApartments`, from
  `IntegerValuationCommonApartmentsProof`, to choose the common translated
  original apartment.
* `KPApartmentData.map_torusUnits_smul_apartmentMap`, from
  `ScalarTorusUnitsFixApartment`, to show that bounded points of its torus
  fix the entire translated apartment. The proof uses the actual
  rational-point conjugation formula and the group action. Functoriality
  of the character-valuation kernel supplies the other subgroup condition.
* `IsMaximalSplitTorus.comp_iso`, from `Rational.SplitRankTransport`, to
  retain generic maximality under this actual inner automorphism.
* `IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded`,
  from `IntegralModel.SplitTorusBoundedPoints`, to extend that split torus
  as a closed split torus of `N`. The actual unramified integer ring is a
  DVR, its residue field is algebraically closed and hence infinite,
  and its units have normalized valuation one.

The generic maximality lemma concerns the conjugated inclusion in `G`.
No descent of this torus, special torus over `F`, centralizing conjugator,
or coefficient-stable apartment is asserted here. Those are additional steps
in the host special-apartment problem.
