# Actual local determinant characters and standard diagonals

For every Hecke character of an actual number field of arbitrary universe,
`finiteLocalDeterminant_eq_finiteComponent_det` identifies the existing
local character obtained by restricting the full adelic determinant
character with the existing local Hecke character composed with the
local matrix determinant. The rank is any natural number. The proof uses
the actual compatibility of the full adelic determinant with the existing
identity-supported finite local insertion; it then applies the character.

`finiteUniformizerValue` is the local Hecke character evaluated on the
chosen uniformizer unit of the existing canonical p-adic completion data.
It introduces no new uniformizer or normalization.
For every positive rank `r + 1` and every standard index
`i : Fin (r + 2)`, `finiteLocalDeterminant_standardDiagonal` identifies
the actual local determinant character on the existing standard diagonal
with `finiteUniformizerValue ^ i.val`. This includes both endpoint indices.
The proof expresses the diagonal as the existing subset torus on the first
`i.val` coordinates, computes its actual determinant, counts those
coordinates, and applies preservation of powers by the local character.

Provenance is internal composition of the actual adelic factor identities,
the existing Hecke character and completed-local definitions, and the
published subset-torus determinant and standard-diagonal identities.
The statements require neither finite character order nor local
unramifiedness. They do not claim independence from a change of chosen
uniformizer, spectral existence, Satake classification or Weil/Galois
compatibility.
