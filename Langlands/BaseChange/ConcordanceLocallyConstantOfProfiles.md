# Local constancy of concordance from regular orbital profiles

`concordanceLocallyConstantOfProfiles` proves
`ConcordanceLocallyConstantOfProfilesStatement`, conditional on
`RegularTransferProfileExistenceStatement`. It takes a cyclic algebra with
its module topology over a characteristic-zero nonarchimedean local field,
Borel structures on the two general linear groups, and fixed ambient Haar
measures. For arbitrary Schwartz–Bruhat tests downstairs and upstairs, the
truth value of `ConcordAt` is locally constant on the subtype of associated
pairs whose base matrix is regular semisimple.

Start at a regular orbit and choose a compact open neighbourhood in
the regular locus. Saturate it by ordinary or twisted conjugation.
The saturation is open because each conjugation is a homeomorphism.
It is closed because the ambient characteristic coefficients identify
it with the preimage of a compact set. On the twisted side these are
the characteristic coefficients of the ordered norm. The cyclic norm
lemma, scalar extension of characteristic polynomials, and ordinary
regular conjugacy identify the regular fibers with twisted orbits.

Restrict the test to this invariant clopen set and extend by zero.
The resulting test is regularly supported, still has compact support,
and has the original orbital integral at every point of the saturation.
The supplied regular profiles therefore give local constancy for the
original test along the regular locus. On a regular associated pair
the two profile measure choices are associated. Their one integral
equality is equivalent to `ConcordAt` by the Library's comparison of
associated measures. This transfers local constancy to the comparison
with all compatible associated measures.

This is an internal consequence of the regular orbital integral construction
of Henniart–Lemaire, I.2.7, printed pp. 19–21. It implements the local
constancy used in the rational approximation argument in I.6.8.
