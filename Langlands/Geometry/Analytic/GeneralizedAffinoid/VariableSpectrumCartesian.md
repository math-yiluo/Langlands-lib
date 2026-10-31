# Cartesian quotient arrows and their actual spectra

This internally derived module extends the canonical spectrum restriction
comparison to every Cartesian arrow of the actual varying-group quotient
category. It uses Mathlib's full Cartesian universal property and its
uniqueness isomorphism for domains of Cartesian arrows. The motivating
operator-group convention and fibration assertion are Berkovich,
*Étale equivariant sheaves on p-adic analytic spaces* (unfinished 1996
manuscript), section 1.1, printed/PDF pages 2–3, registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
The PDF member has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The exact Cartesian comparison and spectrum preservation here are internal
categorical consequences of the constructed quotient restrictions and their
actual spectra; they are not attributed as separate assertions to that
manuscript.

For a quotient arrow `h : X → Y` that is Cartesian over its original
continuous group homomorphism, `cartesianRestrictionIso h` identifies `X`
with canonical restriction of `Y` along that homomorphism. The comparison
is over the identity of the original source group and its homomorphism
followed by the canonical restriction arrow equals the complete original
arrow. Both assertions are consequences of Mathlib's Cartesian unique-lift
construction.

`spectrumFunctor_map_isStronglyCartesian` maps this comparison isomorphism
through the actual spectrum functor. The group component remains the
identity because the spectrum functor retains group maps. Isomorphisms
with this lift property are strongly Cartesian; the previously constructed
canonical spectral restriction is strongly Cartesian as well. Mathlib's
composition theorem and the mapped full factorization identify their
composite with the spectrum of `h`, proving the claimed full universal
property against every continuous source action.

The coefficient field is any ultrametric normed field in universe `u` and
operator groups are independently in universe `v`. All arrows and their
spectra retain the original quotient algebras, bounded maps and topologies.
The proof concerns the constructed quotient and jointly continuous action
categories and does not identify their continuity conventions with an
analytic automorphism topology.
