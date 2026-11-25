# Inner equivalence of Galois pullbacks from all-test inner discrepancy

Internal support for `InnerFormStarActionStatement`, derived from the
published equivalence between natural local group isomorphisms and actual
isomorphisms over a cover, and from the all-refinement inner-discrepancy
interface. This is the forward counterpart of the published finite-Galois
base-change discrepancy construction.

`IsAdjointQuotient.exists_basePointIso_trans_eq_pullIso_of_innerDiscrepancy` takes
an actual isomorphism after a field extension whose induced local family has
inner discrepancy. For every endomorphism of the field cover over the original
field, it constructs a section of the base-changed adjoint quotient whose inner
automorphism followed by the original isomorphism equals its canonical pullback.
The proof evaluates the all-test discrepancy at the identity cover point and the
chosen endomorphism, then uses the recovery equivalence to identify the actual
isomorphisms. The cover endomorphism need not be invertible, and the field
extension need not be finite.

`IsAdjointQuotient.innerEquivalent_pullIso_of_innerDiscrepancy` expresses the same
conclusion as fppf-local inner equivalence. It uses the full-centre fppf quotient
and its conjugation restriction to turn the adjoint section into a locally inner
automorphism, then cancels the comparison isomorphism.

`IsFppfInnerEquivalent.pullIso` transports an inner equivalence through pullback
and the two canonical descent comparison isomorphisms.
`isFppfLocallyInner_innerIso` gives the identity-cover witness for conjugation by
a rational point. These two lemmas will allow torus and base alignment without
changing the inner-equivalence condition on Galois pullbacks.

`IsAdjointQuotient.InnerPullComparisonStatement` explicitly defines the
Prop-valued comparison assertion for the supplied quotient, field extension,
and two groups. `IsAdjointQuotient.innerPullComparison` proves it by applying
`innerEquivalent_pullIso_of_innerDiscrepancy` to each comparison, its all-test
innerness condition, and every cover endomorphism.
