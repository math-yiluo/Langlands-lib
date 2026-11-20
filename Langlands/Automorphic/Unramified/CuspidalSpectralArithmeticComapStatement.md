# Spectra of arithmetic pullbacks of cuspidal classes

`SpectralSystem.reindex` takes an equivalence from the original place set
to the new one, maps the finite exceptional set forward, and at each new
place assigns the old eigenvalues at its inverse image. For a field
isomorphism `e : K ≃+* L`, `finitePlaceEquiv e` sends a place of `L` to
its restriction along `e` in `K`.

`Langlands.Automorphic.Unramified.CuspidalSpectralArithmeticComapStatement`
asks that a genuine spectral presentation of an actual cuspidal class
transport to the arithmetic pullback of that class, with the indicated
reindexed spectrum. The same local factor universe is used on both sides.
Pullback commutes with the finite adelic action on the actual finite slice.
The transported completed-field isomorphisms identify the integral groups,
the spherical Hecke operators, and the normalizing residue cardinalities.
This makes it possible to use the reindexed spectra as genuine attachments
for every Galois conjugate in an isobaric orbit.

This is a derived interface for the transport implicit in Arthur–Clozel
(1989), III.1.1, printed p. 199, and III.4.4(iii), printed pp. 210–211.
When `e` is the inverse of a Galois automorphism the actual pullback is
`IsoClass.galoisConj`. The hypotheses of the interface supply the original
attachment. Transport of this attachment is the only existence assertion.
