# Distance-additive composition of actual continued compact operators

`DynamicCommonLeviPresentations.exists_continuedPair_comp_smul` gives the
composition law for three actual continued pair operators at their common
regular parameters. The scalar is fixed and positive, and it accounts for
the Haar measures of the original pair operators. The inducing
representation is irreducible and admissible.

`exists_galleryIntegralOperator_comp_smul` gives the composition for the
represented gallery operators with their fixed Haar measures when the
three pairs are `PQ`-regular. For each pair,
`continuedPairGalleryScale` and
`representedContinuedPairOperator_compact_apply` give the change from that
operator to the actual compact continuation. Multiplying the two changes
for the consecutive pairs and dividing by the change for the direct pair
gives the scalar in the theorem.

`exists_generic_galleryRegular` supplies one principal open for the three
pairs. `intrinsicGalleryCoefficient_twist` identifies the twists on the
represented and literal Levi schemes. The intersection of this open with
the three denominator nonvanishing sets is open and dense. The
composition remains rational on the full common regular region, so
`rationalUnramifiedOperator_eq_of_eqOn_isOpen` extends the equality there.

This is the distance-additive composition of Waldspurger IV.1(12), printed
p. 283, with the fixed Haar comparison factors of the Library's represented
operators. Source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
