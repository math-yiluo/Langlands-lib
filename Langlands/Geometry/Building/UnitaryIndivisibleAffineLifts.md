# Indivisible affine lifts from supplied multipliable unitary depths

This internal module combines the exact coordinate-to-affine-root
bridges with the finite-tower central-jump theorem. The apartment is supplied;
the coordinate and depth comparison premises remain explicit.

For an actual affine root with derivative `a`, if no relative root `b`
satisfies `2b = a`, the affine root is indivisible. Otherwise an affine half
root would have some actual relative derivative `b`; twice its reduced
root form would equal the form of `a`. Evaluating on representatives in
`V(S)` and using faithfulness of character evaluation for a split torus
would force precisely `2b = a`.

Now supply quadratic unitary coordinates for `a`, assume both `a` and `2a`
are relative roots and `4a` is absent, and identify the depth at one point
`x` with the literal coordinate depth `depthA w`. If `w` has an indivisible
central jump `r`, construct the affine functional with derivative `2a`
and value `r` at `x`. The doubled-root bridge makes it an ordinary affine
root. Its affine half has derivative `a` and value `r/2`; the ordinary
bridge would turn membership of that half into the excluded quotient
jump. The constructed affine root is therefore indivisible.

For the original base-normalized henselian tower valuation, the arithmetic
premise follows from `SU3Root.tower_hasIndivisibleCentralJump`. The finite
dimensionality of the coordinate base field over the original field is
inferred from the finite dimensionality of the coordinate extension
already carried by `RootUnitaryCoordinates`.

`HasMultipliableUnitaryTowerDepths` requires these actual unitary coordinates
and an exact tower-depth comparison only for relative roots with a double.
Their origins can be chosen separately within the supplied apartment. Under
this premise, splitness of the prescribed torus, surjectivity of the integer
base valuation, henselianity, and absence of quadruple relative roots,
`hasIndivisibleDerivativeLifts_of_unitaryTowerDepths` proves the full
`HasIndivisibleDerivativeLifts` property for that apartment. Given a derivative
witness, the proof keeps it when its relative derivative has no half root
and uses the constructed doubled-root lift otherwise. This retains
multipliable derivatives and makes no characteristic or residue-field
restriction.

The argument is an internal composition of actual root forms, the two
coordinate jump bridges and the finite-tower arithmetic, with no local
classification or Kneser–Tits input. It does not prove existence of the
actual coordinates or their exact depths for every quasi-split group and
supplied compatible apartment. Those obligations are discharged by
`QuasiSplitHenselianUnitaryDepths` and `AlgebraicRankOneCoordinatesExistenceProof`,
which `QuasiSplitIndivisibleDerivativeLiftsProof` composes into the
unconditional `QuasiSplitIndivisibleDerivativeLiftsStatement`.
