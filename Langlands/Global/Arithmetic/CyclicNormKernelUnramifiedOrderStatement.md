# The local order of a cyclic norm-kernel character

`Langlands.Global.HeckeCharacter.CyclicNormKernelUnramifiedOrderStatement.{uF,uE}`
concerns the local value of an actual Hecke character `η` whose kernel is the
idele-class norm image for a cyclic Galois extension `E/F`. On one cofinite
set of finite places `v` of `F`, the character is unramified and every place
`w` above `v` has ramification index one. The order in `ℂˣ` of
`η.finiteUniformizerValue v` equals the actual residue degree `f(w/v)` at
each such `w`. At these places the uniformizer value is independent of the
choice of uniformizer. The fields have independent universes.

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), Chapter III, Theorem 3.1, printed p. 201, use this
order to match the product of the local factors of the norm twists with the
product over the places above `v`. Chapter III, §6, printed pp. 215–217,
uses the same local calculation in prime degree in equations (6.1)–(6.6).
The statement isolates the arithmetic input for both uses. Faithfulness on
the norm quotient is required to obtain the exact order. An arbitrary
character trivial on norms would give only divisibility by the residue degree.

For a proof using Library results, the norm-reciprocity argument in
`CyclicNormKernelCharacterProof` descends the Galois projection along the
surjective relative Weil transfer. It identifies its kernel with the actual
norm image using `RelativeWeilGroup.transfer_inclusion`. At an unramified
place, `RelativeWeilGroup.exists_transfer_eq_inv_ofAdicCompletion` maps a
local degree-one element to the inverse of a uniformizer class. The local
relative Weil map projects this element to a Frobenius whose order is the
residue degree. This order can be read from the kernel of the local
projection on the relative extension, using the description of the image
of the completed Weil map by degree divisibility. Taking inverses leaves the
order unchanged. The mixed-universe case can use the base-image comparison
from `CyclicNormKernelCharacterProof` and transport the finite components
and their uniformizer values along the base-field isomorphism.
