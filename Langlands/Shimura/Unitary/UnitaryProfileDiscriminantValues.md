# The local discriminant values of an even unitary profile

`unitaryProfileDiscriminantValues` takes an `InitialUnitaryProfile` on
the supplied CM extension in even degree \(n>1\), with split-place
certificates for its finite support. It supplies the cohomological
class and all four localization formulas required by the even norm
correction.

Choose a finite Galois splitting presentation of the initial
algebra over the base field's universe, and take the class of its
unitary discriminant through the Brauer comparison. At a chosen
split place, use the specified positive upper place to evaluate
the half-degree multiple of its invariant. At other split places
that multiple is zero. The nonsplit finite formula uses the signed
determinant of the initial local Hermitian chart, and the real formula
uses the initial signature at the embedding of the place. These are
the actual fields and places in the profile, with the two number
field universes independent.
