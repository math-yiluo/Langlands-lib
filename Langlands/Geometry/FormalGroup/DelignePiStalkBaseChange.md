# Actual rational Pi and its integer powers under inverse image

This module proves compatibility of the actual total rational Pi automorphism
with the constructed F-linear inverse-image stalk comparison. The result holds
for every integer power, including negative powers. It uses the existing
operators and comparisons from `DeligneRationalSheaf`,
`DeligneDeterminantLattice`, `DeligneLatticeBaseChange` and
`DeligneRationalStalkBaseChange`.

## Source and scope

The source motivation is V. G. Drinfeld, *Coverings of p-adic symmetric regions*
(1976), Section 2 A, printed pages 109–110 (PDF pages 3–4): the graded
O[Pi]-sheaf on page 109, its rational frame at the page boundary, and the
integer Pi-translates in condition (c) at the beginning of page 110. The
registered source is `drinfeld-1976-coverings-p-adic-symmetric-regions`,
with content SHA-256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The construction and compatibility results here are derived infrastructure
for transport of that determinant condition.

The hypotheses are a commutative ring O, a field F with an O-algebra structure,
a positive natural number d, an element pi of O whose image in F is nonzero,
and an arbitrary continuous map f : X → Y. The sheaf M on Y is an actual
module sheaf over `PiAlgebra d pi`. No flatness, graded decomposition or frame
is needed for these operator equations. The nonzero image of pi is exactly
the hypothesis used by the existing `rationalPiAut` construction to make Pi
invertible, using its d-th power relation.

The comparison is the actual `rationalLatticeStalkPullbackIso`; no comparison
or operator equivariance is supplied as extra input. This module does not yet
transport the translated frame lattices or exterior-power lattices and does
not assert determinant normalization, integral injectivity, full
admissibility or representability.

## The actual sheaf and stalk squares

`inverseImageRationalLatticeIso_pi` proves that inverse image of the forward
map of the actual rational Pi automorphism, followed by the total rational
sheaf comparison, equals that comparison followed by the actual rational Pi
on the pulled sheaf.

The proof uses `rationalPiAut_hom` to identify each forward map with
rationalization of integral `latticePi`. It then applies naturality of
`inverseImageRationalIso` to that integral operator. The remaining equation is
rationalization of `inverseImageLatticeScalarIso_pi`, which already
intertwines the actual integral distinguished operators. Functoriality of
rationalization completes the square. Thus this compatibility concerns the
actual automorphisms even though it is proved by their forward morphisms.

`rationalPiStalkAut_pullback` proves the corresponding square on actual
rational stalks, from the original point f(x) to x on the inverse-image
sheaf. The proof applies the sheaf-to-presheaf/stalk composite functor to the
preceding square and uses `inverseImageStalkIso_naturality` for the original
rational Pi morphism. This is the naturality of the constructed stalk
comparison, not a chosen presentation of the stalk as a tensor product.

## Transport as an automorphism and all integer powers

`rationalPiStalkPullbackAut` transports the original actual rational Pi
through the actual stalk isomorphism e by `Aut.autMulEquivOfIso e`. Its
forward map is `e.inv ≫ Pi.hom ≫ e.hom` on the pulled rational stalk.

`rationalPiStalkPullbackAut_eq` proves that this transported automorphism is
the actual `rationalPiStalkAut` on the pulled sheaf. Extensionality reduces
to the forward maps; the preceding stalk square and cancellation of e with
its inverse give the equality.

`rationalPiStalkAut_zpow_pullback` proves the stalk square with Pi replaced
by Pi^n for any n in the integers. The proof uses the multiplicative
equivalence `Aut.autMulEquivOfIso e` and the general `map_zpow` identity.
Substitution of `rationalPiStalkPullbackAut_eq` identifies the transported
operator with the actual pulled operator. Finally, precomposing the
forward-map equality with e and canceling `e.hom ≫ e.inv` gives the desired
intertwining equation. Negative powers follow from this group identity
without adding a separate inverse or a new invertibility assumption.
