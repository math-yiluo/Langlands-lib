# Genuine cuspidal spectra in an independent factor universe

`Langlands.Automorphic.Unramified.CuspidalSpectralAttachmentExistenceStatement`
asks for a numerical spectrum genuinely attached to each supplied actual
cuspidal realization. `IsoClass.hasSpectralSystem_iff` identifies such an
attachment with a spectral presentation of the very same realization.
The local factors of that presentation are in an arbitrary universe `uV`
independent of the number field universe `uF`. The numerical coefficients
are complex and the spectrum has positive rank `r + 1`.

Flath (1979), *Decomposition of representations into tensor products*,
§§2–3, especially Theorem 3, printed pp. 180–182, supplies the tensor product
setting behind the existing constructions. The universe requirement here
is a derived Library interface. The published
`cuspidalIrreducibleAdmissibleFiniteSliceExistence` chooses an actual
irreducible admissible finite slice, and the theorem
`CuspidalOperatorRealization.exists_presentation_of_finiteSlice` presents
it with irreducible admissible local factors in the field universe.
`CuspidalSpectralUniverseLift` already raises the factor universe.

To reach an arbitrary factor universe, each irreducible smooth local
factor can be realized on a small carrier. A nonzero vector has an open
stabilizer, so its orbit in the second-countable local group is countable.
Irreducibility makes its complex span the entire factor, which then has a
small carrier described by finite complex linear combinations. Transport
references, the restricted tensor product and the comparison with the
actual finite slice along equivariant linear equivalences of these local
factors. This retains the same actual spectral data and uses the existing
construction over the field universe. For `uF = 0`, the published raising
construction suffices directly.

This existence input is needed at the degree-one end of the cyclic
transfer tower. Weak transfer in Arthur–Clozel III.1.1, printed p. 199,
uses a genuinely attached spectrum at every degree.
