# Rationalization and the total Deligne operator

This is a derived sheaf construction for Drinfeld, *Coverings of p-adic
symmetric regions* (1976), Section 2 A, printed p.109 (PDF p.3), final
paragraph, and printed p.110 (PDF p.4), opening paragraph and condition (c).
The registered source is `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source uses the rational sheaf, its frame and integer powers of Π in the
determinant normalization. This module constructs the rationalization and an
actual invertible total operator needed to give those powers a meaning.

For a commutative ring O, an O-algebra field F and a topological space X,
`rationalPresheafFunctor` sends an actual O-module sheaf M to the presheaf
whose sections are F ⊗_O M(U), with the actual extended restriction maps.
`rationalSheafFunctor` then applies categorical sheafification in F-modules.
`rationalRestriction` restricts an F-module sheaf to O. All rings, spaces and
section modules use the common universe of the preceding Deligne modules.

`rationalUnit` is an actual O-linear sheaf morphism from M to the restricted
rational sheaf. It sends an integral section m to the sheafification image
of 1 ⊗ m. It is formed from the scalar-extension adjunction's unit and
the sheafification unit. `rationalUnit_naturality` proves that this map
commutes with every O-linear sheaf morphism. No injectivity or stalk tensor
comparison is asserted.

For any actual O[Π]-module sheaf M, where O[Π] is the constructed quotient
O[X]/(X^d − π), `rationalLattice` rationalizes its underlying O-module sheaf.
This construction may be applied to the sheaf of a `LatticePiSheaf`; it
does not need flatness or a chosen grading. `rationalPiPresheaf` applies
scalar extension to multiplication by the distinguished quotient element.
`rationalPiPresheaf_pow_tmul` identifies every natural power on a pure
tensor with the tensor of the corresponding integral-operator iterate.

`rationalPiPresheaf_relation` proves that the d-th power of this actual
presheaf endomorphism is the scalar endomorphism given by the image of π
in F. The proof reduces to pure tensors, uses the integral quotient
relation, and moves π across the tensor unit by its O-linearity. When
d is nonzero and the image of π in F is nonzero, that scalar endomorphism
is a unit; the nonzero-power criterion for units then proves
`rationalPiPresheaf_isUnit`.

`rationalPiAut` takes the resulting presheaf automorphism through the
sheafification functor, producing an actual automorphism of the total
rational lattice sheaf. `rationalPiAut_hom` identifies its forward map
with rationalization of the original integral operator. Its inverse
comes from the proved unit property. Thus its automorphism group has
integer powers; no separate invertibility field is assumed.

The derived provenance is the explicit composition of tensor extension,
the two unit maps, and sheafification, together with the quotient power
relation and elementary unit algebra. The hypotheses are more general
than a discrete valuation ring and its fraction field. This module does
not impose Drinfeld's conditions (a)–(c), identify determinant lattices,
construct isomorphism classes or base change, define the PGL action,
or prove representability or a generic-fibre comparison.
