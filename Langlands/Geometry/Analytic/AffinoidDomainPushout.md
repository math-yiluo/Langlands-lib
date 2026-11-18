# Restricting an affinoid pushout to a domain of one factor

`swapMap` interchanges the two legs of the bounded affinoid pushout by
its universal property. Applying this comparison twice gives the identity,
as can be checked on both legs. `swapEquiv` packages the resulting bounded
equivalence between the pushouts in the two orders.

`domainPasting f g D` represents the inverse image of a domain `D` of
the second factor in the original pushout spectrum. Its algebra is the
direct pushout of `f` and the composite of `g` with the domain's
structural map. The proof starts with the existing domain base change
along the second pushout leg. It transports that full representation
across the bounded pasting equivalence. The equivalence computes the
new structural map as the actual comparison from the old pushout to
the direct restricted pushout.

`small_spectrum_of_domain_finiteBanach` applies finite Banach base change
to the original pushout when the first leg is finite Banach. After
exchanging the factors, the spectrum of the restricted pushout embeds
in that small spectrum by the full domain embedding theorem. Exchanging
the factors back proves smallness in the universe of the second factor
spectrum.

The provenance is internal. The proof uses the published bounded
pushout, domain base change, pushout pasting, and finite Banach
base change constructions.
