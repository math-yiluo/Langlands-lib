# From finite polarization diagonals to integral alternation

`integralPolarizationWeilAlternation` proves the conditional proposition
`IntegralPolarizationWeilAlternationStatement`.

The finite helper `finiteWeilAlongPolarization_self` precomposes the
scheme-morphism equality supplied by the exact
`RelativeFiniteWeilAlternationStatement` with an arbitrary test-scheme
point of the actual torsion kernel. The composition of this point with
the diagonal is the product lift of the point with itself. Precomposition
of the constant identity is again the identity. The published finite
bilinear-map application formula therefore gives additive zero for the
finite pairing at that point. The helper retains the actual
`IsPolarization` hypothesis and all of its construction inputs.

For `integralWeilAlongPolarization_isAlt`, two elements of the twist
inverse limit are equal if all their roots-of-unity coordinates are
equal. The existing coordinate comparison identifies the polarization
pairing at each positive selected order with the finite pairing above,
transported through the torsion-kernel and roots-of-unity equivalences.
The finite helper makes it zero, and the additive roots equivalence
preserves zero. This works for every order predicate, including the
full system.

`awayWeilAlongPolarization_isAlt` uses the same equality for the selected
orders coprime to the modulus; the away bilinear map has the identical
underlying value. `primeWeilAlongPolarization_isAlt` repeats the
coordinate argument at the positive orders `p^n`, using `Fact p.Prime`
to establish positivity. The final theorem packages the three
conclusions.

The argument is an internal deduction from the exact finite statement
and the existing coordinate comparisons. It does not prove the deep
relative finite alternation or transition statements, both of which
remain explicit hypotheses. It uses all test schemes, retains the
actual twists and their scalar rings, and asserts no perfectness or
nondegeneracy.
