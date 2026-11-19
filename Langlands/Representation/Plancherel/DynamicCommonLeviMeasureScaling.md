# Change of compact Haar normalization for actual common-Levi intertwiners

For a pair of dynamic parabolics, the standard quotient is the left coset space
of the intersection in the target radical. The two intrinsic Haar measures on
the radical and the intersection each normalize the preimage of the chosen
ambient compact open subgroup to have mass one.

`pairQuotientHaarScale` is the target-radical Haar scale divided by the
intersection Haar scale. Both factors are strictly positive. The proof of
`pairQuotientMeasure_changeCompact` first compares the two actual quotient
measures by right invariance and regularity. The Weil integral formulas then
identify their proportionality factor with the ratio of the two Haar factors.
A compactly supported continuous test with nonzero target-radical integral
allows cancellation.

`pairFullDomainRegion_changeCompact` uses invariance of the smooth weak integral
domain under positive finite measure scaling. `pairFamily_changeCompact`
rescales the representing vector for each source input and ambient evaluation
point and uses uniqueness of the weak integral. This gives the scale relation
for the actual intertwining maps between the original normalized inductions.
All conclusions are derived from the Library's actual measures and weak
integrals.
