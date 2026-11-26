# Arithmetic pullback of an attached cuspidal spectral system

The proof takes the actual cuspidal realization and spectral presentation
witnessing the attachment. Arithmetic pullback carries its nonzero finite
slice to a finite slice of the pulled-back realization. The tensor transport
reindexes the factors, exceptional set and reference vectors. Each factor
retains its original carrier, with the local action pulled back along the
completion group isomorphism.

At a place outside the transported exceptional set, irreducibility and
admissibility pull back along the local topological group equivalence.
The old and new embedded components each come with an equivalence from the
corresponding factor. Composing these equivalences compares the actual local
components even when their chosen tensor tails differ. The local spherical
transport theorem transfers the full set of normalized Hecke scalar equations,
so the new presentation can reuse the original eigenvalues at the corresponding
place.

The attached system of the new presentation therefore has equal Euler
polynomials at every pair of corresponding places where the polynomials are
defined. The inverse place map agrees with the place map of the inverse field
isomorphism by contravariant composition. The pointwise equality implies the
cofinite assertion in `CuspidalArithmeticSpectralTransportStatement`.

The proof is an internal consequence of the Library's arithmetic pullback,
finite tensor reindexing and local spherical compatibility, with independent
universes for the two number fields and the factor carriers.

`arithmeticPlace_inverse` identifies pullback of a finite place along the inverse field isomorphism with the inverse equivalence on finite places.
