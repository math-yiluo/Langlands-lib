# Determinants and finite adelic factor maps

This internal construction specializes Mathlib's continuous determinant to the
actual finite adelic matrix group over a number field `F : Type uF`. The rank
`n` is any natural number, including zero. `FiniteAdelicGL.determinant` takes
values in the existing finite idele group, with its units topology. No new
restricted product, completion, group action or topology is selected.

`determinant_localProjection` is the naturality of the matrix determinant
under evaluation at a finite place. `determinant_localInclusion` proves that
inserting a matrix at one finite place and the identity elsewhere inserts its
local determinant at that place and `1` elsewhere. The proof checks each
finite component, using naturality and the existing singleton projection laws.

`AdelicGL.determinant_ofFinite` proves compatibility with the existing insertion
of the whole finite factor into the full adelic matrix group. It checks the
infinite and finite coordinates of the underlying idele: the infinite
coordinate is the determinant of the identity matrix and the finite coordinate
is the finite determinant. Combining these results gives
`determinant_ofFinite_localInclusion`, equality with the existing local idele
insertion into the full idele group.

The provenance is internal: the definitions in `Global/Adelic`,
`Global/AdelicGL` and `Global/FiniteAdelicGL/LocalFactor`, Mathlib's determinant
naturality and the determinant of the identity matrix supply all inputs.
These are identities between actual maps. They assert no class-field,
automorphic spectral, local reciprocity or global matching theorem.
