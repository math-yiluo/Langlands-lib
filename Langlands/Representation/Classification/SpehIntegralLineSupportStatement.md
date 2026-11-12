# A single integral cuspidal line for Speh representations

`Langlands.Classification.SpehIntegralLineSupport F T` states that every
actual representation `S` satisfying `d.IsSpeh S` has a supercuspidal support
multiset `s` and a cuspidal datum `ρ` such that each occurrence in `s` is
`ρ.twist m` for an integer `m`. The field and representation universes are
independent. The cuspidal data and the supplied representation both use the
representation universe `max uF uV`.

The support predicate is the Library's actual subquotient-of-cuspidal-induction
predicate. The statement assumes neither unitarizability of `S` nor a
multisegment classification. The existing `IsSpeh` hypothesis includes the
discrete-series condition on `d.delta` and an actual irreducible quotient map
from the centered induction.

This is a derived prerequisite for complementary Speh irreducibility. Its
provenance is the published segment classification of essentially
square-integrable representations, compatibility of segment heads with real
twists, and the actual cuspidal quotient construction for products of segment
heads. If `Δ` is a segment for `d.delta`, the cuspidal members of the centered
product have exponents `(d.length - 1)/2 - i + j` relative to `Δ.base`.
Taking `ρ = Δ.base.twist ((d.length - 1)/2)` leaves the integral exponent
`j - i`. This explanation gives the intended derivation; this statement
module does not assert a proof.
