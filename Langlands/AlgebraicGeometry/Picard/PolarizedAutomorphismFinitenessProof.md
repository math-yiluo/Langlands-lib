# Proof of finiteness of the actual integral polarized automorphism group

`Langlands.AbelianScheme.polarizedAutomorphismFiniteness` has type
`PolarizedAutomorphismFinitenessStatement.{u}` for arbitrary `u`. It proves
finiteness of the subgroup of actual integral automorphisms preserving the
given geometric polarization over an algebraically closed characteristic-zero
field, with the construction prerequisites quantified in the statement.

The proof applies `polarizedAutomorphismFiniteness_of_rosati_and_lattice`.
`Rosati.rationalInverse` supplies rational invertibility of the given
polarization, and `Rosati.positivity` supplies symmetry and strict positivity
of its actual rational Rosati trace form. Specializing `homFiniteFree k A A`
gives finite freeness over `ℤ` of the integral endomorphism module of `A`.

The lattice reduction uses `fieldDualSchemeMapAdditivity` and sends each
polarized automorphism to its underlying integral endomorphism. Preservation
of the polarization forces the diagonal value of the integral trace form on
that endomorphism to equal the geometric trace of the identity. Injectivity
of rationalization transfers strict positivity to the integral endomorphism
lattice. The finite-lattice theorem clears denominators in a Gram matrix to
prove that the sublevel set at the trace of the identity is finite. The
injective map into that set gives finiteness of the group.

This is the algebraically closed characteristic-zero case of J. S. Milne,
*Abelian Varieties*, corrected author revision of January 2, 2022, §17,
Proposition 17.5(a), p. 37 (registered source
`milne-abelian-varieties-1986-author-2022`). Milne's proof uses the discreteness
of the endomorphism lattice and compactness of the real Rosati level set.
The Lean proof uses the finite rational sublevel set described above.
