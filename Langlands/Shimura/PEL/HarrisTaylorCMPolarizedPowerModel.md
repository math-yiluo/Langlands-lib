# A polarized integral model for an even power of a CM self-isogeny

This internal construction works at the identity point of an algebraically
closed characteristic-zero field spectrum with the existing Harris datum,
positive polarized rational action, and compatible frame tower.

`PolarizedIntegralPowerModelWitness` strengthens the exact integral power-model
witness. It retains a compatible frame, a positive integer m, the relation
q^(2m)=1, the same realizing scheme B, the same exact rational comparison r,
the exact full integral Tate lattice equality, and both rationalization equations
for the integral automorphism g. It also includes actual dual data W on this B
and an actual geometric polarization lam with the integral equation
`g.hom ≫ lam ≫ W.map P W g.hom = lam`.

`polarizedIntegralPowerModelWitness_of_levelIso_fixed` constructs this witness
from fixedness of an orbit at any original compact Harris level. The displayed
dual-existence premise is precisely the dual-existence field available in
`AdmissibleCMBase`; it does not assert universal dual existence. The proof first
uses the existing integral power-model constructor. It chooses actual dual data
for the scheme thereby obtained, uses the existing isogeny-model polarization
on this same scheme and exact comparison, and applies the proved integral
polarization-transport theorem with exponent 2m. The multiplier-one relation
already belongs to the integral power-model witness.

`finiteOrder_of_integral_conjugate_power` is a generic categorical helper.
It maps an actual integral automorphism into the rational endomorphism monoid,
transfers its finite order through the monoid equivalence given by the exact
comparison, and then uses positivity of the power exponent to recover finite
order of the original rational endomorphism.

`finiteOrder_of_polarizedIntegralPowerModelWitness` applies that helper to the
same witnesses. It is conditional on the finite-order consequence of finiteness
of actual integral polarized automorphisms over this field. That geometric
theorem remains a separate input; no finiteness or rigidity theorem is claimed
here. All imported statements are reused without modification. The provenance
is an internal composition of the exact integral model, actual polarization
transport, categorical conjugation, and elementary finite-order lemmas.
