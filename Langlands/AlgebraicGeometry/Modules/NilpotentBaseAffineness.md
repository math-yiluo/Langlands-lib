# Affineness across a nilpotent base reduction

`Langlands.AlgebraicGeometry.Modules.NilpotentBaseAffinenessStatement`
says that if `X` is locally Noetherian over the spectrum of a Noetherian
ring `R`, `I` is a nilpotent ideal of `R`, and the actual pullback `Z`
over `Spec (R/I)` is affine, then `X` is affine. The theorem
`nilpotentBaseAffineness` proves this proposition in every universe.

The proof uses the structure module of `X` and the Library's ideal-adic
layers. Each successive layer is quasi-coherent and annihilated by `I`.
It therefore comes from its pullback to `Z` by pushforward along the
closed immersion. Affine cohomology vanishing gives zero first cohomology
for each layer, and the resulting surjections compose to give a
surjection on global functions onto `Z`.

The pullback projection is surjective on points because the base ideal
is nilpotent. A global function cutting a basic open in `Z` lifts to
`X`. If its basic open in `Z` lies over an affine open of `X`, pointwise
surjectivity puts the lifted basic open inside that affine open. These
functions give an affine basic-open cover and generate the unit ideal:
their images generate the unit ideal on `Z`, and a lift of `1` has
unit germ everywhere on `X`. The affine basic-open criterion then applies.

This is a derived supporting result for using affine group-scheme moduli
on local Artinian tests. It uses the existing comparison and vanishing
theorems for quasi-coherent structure-module quotients.
