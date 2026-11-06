# The fpqc cover of valuation-integer spectra

This internal construction applies to arbitrary fields `K` and `L` in a
common universe `u`, an algebra structure `K → L`, and valuations `vK` and
`vL` with `Valuation.HasExtension vK vL`. The value groups may lie in
independent universes. The extension condition allows equivalent valuation
normalizations. There is no algebraicity, degree, discreteness,
completeness, characteristic or residue-cardinality hypothesis.

The integer-ring algebra is exactly Mathlib's
`Valuation.HasExtension.instAlgebraInteger`. Its elements map through the
given field algebra map; no replacement coefficient ring is chosen.

## Flatness and the cover

`valuationInteger_flat` proves flatness of `vL.integer` over `vK.integer`.
The source is a valuation ring, hence a Bezout domain. Mathlib's canonical
integer-ring module is torsion-free, so
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` and
`Submodule.isTorsionFree_iff_torsion_eq_bot` give flatness.

Both integer rings are local. Their canonical algebra map is local by
`Valuation.HasExtension.instIsLocalHomValuationInteger`, using the local
field algebra map. Thus `valuationInteger_faithfullyFlat` follows from
`Module.FaithfullyFlat.of_flat_of_isLocalHom`.

`valuationInteger_fpqc` converts faithful flatness to flatness and
surjectivity of the actual `Spec.algebraMap vK.integer vL.integer`.
Quasi-compactness is available for this morphism between affine spectra.

`valuationIntegerCover` constructs a `Scheme.fpqcPrecoverage` cover of
`Spec vK.integer` indexed by `PUnit`. Its sole object is
`Spec vL.integer`, and its map is the original canonical integer-ring
spectrum map, as recorded by `valuationIntegerCover_f`. Cover membership
uses the proved flatness, surjectivity and quasi-compactness.

## Provenance and scope

This is an internal derivation from the pinned Mathlib valuation extension,
torsion-free flatness, local faithful flatness and fpqc site constructions.
It discharges the coefficient-cover conditions needed in supplied-model
descent for valued-field extensions, including infinite extensions. It
does not construct an upstairs comparison isomorphism, a canonical
reductive model, a building, a special point or an exact stabilizer
identity.
