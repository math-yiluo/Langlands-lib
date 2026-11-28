# Transport of regular elliptic character values to the division algebra

For a finite-dimensional central division algebra of reduced degree `n` over
`F`, `transportedEllipticCharacter` reads a complex-valued function on the
regular elliptic elements of `GL_n(F)` at a chosen correspondent of each
regular unit of the algebra. The choice uses `exists_corresponds`, which
realizes the reduced characteristic polynomial on the split side. The
regular elliptic class correspondence is described in Deligne–Kazhdan–Vignéras,
*Représentations des algèbres centrales simples p-adiques*, introduction
(a), printed p. 33. `Corresponds` uses equality of characteristic
polynomials as in Badulescu, *Correspondance de Jacquet–Langlands pour les
corps locaux de caractéristique non nulle* (2002), §1, p. 695.

Over a nonarchimedean local field, suppose that the function gives the
local character values of an admissible representation. Any two matching
split elements give the same value by `HasCharacterValue.conjugate` and uniqueness.
Their common separable characteristic polynomial determines their conjugacy
class. Conjugation in the division group preserves the reduced
characteristic polynomial by matrix conjugation in a splitting chart. In
characteristic zero, multiplying both elements by a common nonzero scalar
preserves matching because both polynomials transform by the same change of
variable. The local character value on the division side therefore inherits
conjugation invariance and the scalar covariance of the split character.

In characteristic zero with the module topology on `D` and the units topology on `Dˣ`,
`isLocallyConstant_transportedEllipticCharacter` uses the continuous family of
split correspondents from `exists_local_regularCorrespondent`. The inverse
image of a neighborhood where the split character is constant gives an open
neighborhood where the transported character is constant.
