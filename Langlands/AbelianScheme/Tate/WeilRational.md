# Rational Weil pairings with the actual Tate twist

This internal construction extends the particular integral Weil pairing of
`WeilIntegral` to the existing rational Tate modules and the existing rational
roots-of-unity twist. It retains the seven tensor/Picard propositions, the
actual abelian scheme and its constructed dual, the inverse Poincare bundle
and evaluation, and the explicit `RelativeFiniteWeilTransitionStatement`.

The private tensor helper first regards an integral bilinear map as a linear
map from a tensor product, extends that map's scalars, and composes with the
inverse of the standard distribution of base change over tensor products.
Currying produces the rational bilinear map. The private scalar-action lemmas
use tensor induction in the scalar and both inputs.

`rationalWeilBilinearMap` uses this procedure on the actual integral Weil
pairing. Its input carriers are `Q tensor_Z Integral` and its output is
`Q tensor_Z` the coherent family of actual roots of unity. The pure-tensor
formula multiplies the two rational scalar factors and applies the original
integral pairing. The canonical-map formula specializes both factors to one.
The uniqueness lemma follows by tensor extensionality in both arguments.

`rationalRestrictAway_rationalWeilBilinearMap` proves that restricting both
inputs and the target to orders coprime to the modulus commutes with the
pairing. Its proof uses tensor induction in both arguments and the integral
coordinate restriction identity.

The two finite-adele action lemmas use the same explicit
`RationalProfiniteIntegerAdeleComparison` on the inputs and the twist.
`adelicWeilBilinearMap` bundles these laws as bilinearity over the existing
`Global.FiniteAdeles Q`. Its value is the rational pairing just constructed.

The analogous prime-to-modulus action lemmas use the integral away bilinear
map and the coupled `PrimeToRationalProfiniteIntegerAdeleComparison h m`
on all three modules. `awayAdelicWeilBilinearMap` bundles the same rational
pairing over `Global.PrimeToFiniteAdeles m`. Both full and away bundles
have application lemmas identifying their values with
`rationalWeilBilinearMap`. The restriction identity above therefore also
compares their underlying pairing values. No roots-of-unity basis or twist
trivialization is chosen.

The provenance is the internal scalar extension of the intrinsic integral
pairing and the published tensor and scalar-action APIs. This unit asserts
no continuity, nondegeneracy, perfectness, alternation, polarization
specialization or monodromy equivariance.
