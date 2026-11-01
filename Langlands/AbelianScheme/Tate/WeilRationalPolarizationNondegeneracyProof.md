# Nondegeneracy of full and away rational and adelic polarization Weil pairings

Author: Worker 147.

`Langlands.AbelianScheme.rationalPolarizationWeilNondegeneracy` proves exactly
`Langlands.AbelianScheme.RationalPolarizationWeilNondegeneracyStatement.{u}`.
The published statement and its imports are unchanged. The theorem retains the
quasi-separated base, actual abelian scheme and polarization, all explicit
dual/Poincare/tensor/Picard and finite-transition inputs, and the algebraically
closed characteristic-zero geometric point `s : Spec K ⟶ S`.

Its four conclusions are two-sided nondegeneracy of the existing full rational
pairing, every away rational pairing, the full adelic pairing for every explicit
scalar comparison `h`, and every away adelic pairing for every coupled `hAway`.
The inputs remain the actual rationalizations over the integers of the integral
Tate limits, and the outputs remain the actual rational roots-of-unity twists.
The convention is the existing second-variable polarization pullback.

## Implemented proof

The proof uses the published prime-coordinate pairings and restricted-product
comparisons. It adds four private coordinate lemmas for an arbitrary commutative
group object `G` and test scheme `T`.

The lemmas `full_eq_zero_of_coordinates` and `away_eq_zero_of_coordinates` use
`GroupScheme.Tate.PrimeComparison.rationalRestrictedProductComparison` and
`rationalAwayRestrictedProductComparison`. Each comparison supplies an additive
equivalence whose coordinates are the actual rational extraction maps.
Extensionality in the restricted product, followed by injectivity of the
equivalence, shows that vanishing of all coordinates implies that a vector is zero.

The lemmas `full_coordinate_surjective` and `away_coordinate_surjective` use the
same comparisons in the other direction. A restricted family supported at one
prime has any prescribed rational vector at that prime. Applying the inverse
equivalence lifts it to the actual full or away rational module. In the away
case the chosen prime must be coprime to the modulus.

The private lemmas `rationalFullWeil_nondegenerate_of_prime` and
`rationalAwayWeil_nondegenerate_of_prime` then prove each radical vanishes.
For a vector in the left radical, lift an arbitrary local test vector by
coordinate surjectivity. The published compatibility identity
`rationalFullToPrime_rationalWeilAlongHomBilinearMap`, or its away counterpart,
identifies the extracted global pairing with the actual prime-adic pairing of
the extracted inputs. The global value is zero, so local nondegeneracy forces
the chosen coordinate to vanish. Joint injectivity of the coordinates gives
the zero global vector. The proof repeats this argument in the other variable
to establish the right radical.

`rationalPolarizationWeilNondegeneracy_of_prime` specializes these lemmas to the
actual polarization at `Over.mk s`. In characteristic zero every prime has
nonzero image in `K`, so `PrimeRationalPolarizationWeilNondegeneracyStatement`
applies at every prime. This gives the full and away rational clauses.
Every natural modulus is covered, including zero and one. At modulus zero the
retained-prime type is empty, and restricted-product extensionality still gives
the required zero-vector conclusion.

For the two adelic clauses, the published formulas
`adelicWeilAlongHomBilinearMap_apply` and
`awayAdelicWeilAlongHomBilinearMap_apply` identify the underlying pairing values
with the rational ones. Unfolding `LinearMap.Nondegenerate`, `SeparatingLeft` and
`SeparatingRight` therefore transfers the two radical arguments. The full
module structures on both inputs and the twist use the same quantified `h`.
The away structures use the same quantified `hAway`, whose type records its
compatibility with `h`. No change of scalar comparison occurs in the proof.

The final theorem discharges the reduction's sole premise with the published
`Langlands.AbelianScheme.primeRationalPolarizationWeilNondegeneracy`:

```lean
rationalPolarizationWeilNondegeneracy_of_prime
  primeRationalPolarizationWeilNondegeneracy
```

Thus the final theorem has no additional nondegeneracy or comparison premise.

## Provenance and scope

This is a derived proof from published Library results. The coordinate argument
is internal algebra using the exact-coordinate additive equivalences in
`Langlands.AbelianScheme.Tate.RestrictedProductProof`. Pairing compatibility
comes from `Langlands.AbelianScheme.Tate.WeilRationalPrimeAlongHom`, imported by
the prime statement. The geometric input is the theorem in
`Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyProof`;
its finite-geometric, dual-kernel and point-divisibility arguments are reused
through that theorem. The original-source provenance of these constructions
and the target is recorded in their paired Markdown.

The result asserts vanishing of both radicals of the four specified actual
pairings. It proves no integral perfectness for an arbitrary polarization,
duality equivalence, continuity or nondegeneracy at arbitrary test schemes.
The Lean proof uses only `propext`, `Classical.choice` and `Quot.sound`.
