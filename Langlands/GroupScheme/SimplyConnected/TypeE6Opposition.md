# Actual E₆ opposition is arm exchange

For an actual Tits index whose entire Cartan matrix is numbered as E₆,
`opposition_eq_symmetry_of_E6_of_corootSpan` identifies actual opposition
with the permutation exchanging 0 with 5 and 2 with 4, fixing 1 and 3.
It assumes that the actual integral coroots span the full cocharacter
lattice. `opposition_eq_symmetry_of_E6` obtains this span hypothesis from
simple connectedness of the group.

Opposition preserves the actual Cartan entries. The finite E₆ symmetry
bound therefore makes its numbered action either identity or arm exchange.
If it were identity, the coroot span and the existing integral
automorphism determination theorem would make the entire based
root-datum opposition automorphism identity. Opposition is the canonical
based representative of minus identity, so the based projection theorem
would put minus identity in the integral Weyl group. The mod-3 obstruction
in `TypeE6NegationWeyl` rules this out.

This is an internal deduction from the actual opposition construction,
the finite Cartan symmetry bound, integral coroot span, and the proved
residue obstruction. It identifies opposition rather than any Galois
element. It imposes no field characteristic, local-field, or rank-one
hypothesis and holds at arbitrary universe.
