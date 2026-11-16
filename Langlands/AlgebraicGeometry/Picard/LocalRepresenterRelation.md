# The equivalence relation of a local presheaf representer

This is an internal construction from the supplied local representing
bijection, extending `LocalRepresenterOverlap`. The universes remain
independent and no sheaf condition is required.

The two projections to the local chart have the same map to the original
base and classify the same family on every test scheme. `kernelLift` and its
projection laws show that every matching pair arises from an overlap point.
`kernel_hom_ext` proves uniqueness using the scheme pullback and the second
projection's covering-base coordinate. The matching-pair property constructs
an involution `exchangeIso` swapping the two projections.
