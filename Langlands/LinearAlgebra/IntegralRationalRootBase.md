# Transfer of an integral root base to a rational root system

This internal construction starts with a reduced integral root pairing, a finite
crystallographic rational root system, a bijection of their full root indices,
and compatible realizations of all roots in a common rational vector space.
The realization of the integral character group is additive and injective; the
realization of the rational root space is linear and injective. The common
ambient space can contain central character directions outside the root span.

An independent integral root family stays independent after the additive
realization, regarded as an integer linear map. Independence over the integers
and rationals is equivalent for vectors in a rational vector space. Reflecting
independence along the target linear realization proves rational independence
of the corresponding roots. Contraposition on pairs of roots and reducedness
of the integral pairing prove reducedness of the rational pairing.

The image of an additive submonoid closure is the closure of the image.
Compatibility of the two root realizations therefore transfers the positive
or negative generation axiom of a supplied integral base. The target
realization is injective, so membership can be reflected to the rational root
space. The alternate base constructor supplies the coroot independence and
generation axioms from these root axioms.

The resulting `base` has exactly the transported simple support. Restriction
of the index bijection gives `supportEquiv`. If rational root-coroot pairings
are the integer source pairings cast to the rationals, this equivalence
preserves every integer Cartan entry, by injectivity of that scalar map.

This is an internal consequence of the imported root-system and localization
results. No actual algebraic-group comparison or existence of the input root
pairings, compatible realizations or supplied base is asserted.
