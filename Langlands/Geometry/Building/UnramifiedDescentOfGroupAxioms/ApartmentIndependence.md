# Uniqueness of the coordinates of a descended apartment

`ReferenceApartmentDescent.eq_on_apartment_of_affine_chart` compares two
parameterizations in the same upper reduced building. The comparison of
lower apartment coordinates preserves closed segments by
`KPApartmentData.smul_apartmentMap_lineMap_of_two_eq`. Midpoint preservation
gives additivity after choosing an origin. Interpolation on the unit
interval then gives real linearity of the map on differences.

The derivative is the identity because `descendedApartment_map_vadd`
gives the same pushforward of real cocharacters for both maps in the
reference chart. Equivariance on the building gives equivariance for the
lower normalizer. The opposite-factor-pair rigidity theorem
`KPApartmentData.val_eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs`
then identifies the original valuation coordinates. This supplies the
parameterization comparison needed when using the fixed apartments of
Kaletha and Prasad, Propositions 9.3.13 and 9.3.16.
