# The characteristic-two B₂ commutator power calculation

This internal derived package performs the exceptional unequal-power
B₂ calculation on supplied actual maps from `Ga R` into an arbitrary
group scheme. The literal convention is
`CommRel u v L : (u(x)v(y))⁻¹(v(y)u(x)) = product(L)`.
All formulas quantify over every affine test scheme.

Assume actual maps `A`, `C`, `V`, `W` satisfy

`CommRel C A [(V,1,1,1), (W,1,2,1)]`

and `2 = 0` in `R`. In the intended application `A` is long, `C` is
short, `V` is the Weyl conjugate of `C` by the `A` representative, and
`W` is the Weyl conjugate of `A` by the `C` representative. Those
root-group and conjugation identifications are not part of this raw-map
package and are not silently assumed.

Let `F` and `F₂` be supplied actual additive-line homomorphisms with
the all-test formulas `x ↦ x^q` and `x ↦ x^(2q)`. The definition
`b2UnequalPowerTerms` annotates the two reversed target terms with
these power maps, new degrees and coefficient one.
`b2_unequal_power_commRel` proves

`CommRel (F₂ ≫ A) (F ≫ C)
  [(F₂ ≫ W,1,1,1), (F ≫ V,1,2,1)]`.

The proof reverses the supplied literal relation. Its output terms
are then `W(-x*y²)` and `V(-x*y)`. In characteristic two,
`-1 = 1`; the exact coefficient balances hold. The degree balances
are `2q = q*2` for the long term and `2*q = 2q` for the short term.
The imported balanced-power transport theorem gives the asserted
formula. No commutation premise is needed for this output order.
`b2_unequal_power_commRel_reordered` exchanges the two terms under
the explicit premise `PointsCommute V W`.

`eraseZeroCommTerms` deletes terms with zero coefficients while
preserving their order. Its actual product is unchanged on every
scheme test, so `CommRel.erase_zero_terms` transfers the formula to
the shortened list. A zero-coefficient singleton is equivalent to
commuting actual points in the directions used by the supporting
lemmas. In particular, `b2_pointsCommute_of_mixed_rel` deduces
commutation of `C` and `V` from the supplied mixed relation
`CommRel C V [(W,2,1,1)]`.

`b2_mixed_unequal_power_commRel` verifies the source mixed relation

`CommRel (F₂ ≫ A) (F₂ ≫ W) [(F ≫ V,2,1,1)]`

under the explicit target premise `PointsCommute A W`. Its left side
is the identity because the target maps commute; its right side is
the identity because its coefficient two vanishes. The package does
not derive this target commutation from a root system.

The provenance is composition of the imported literal reversal,
balanced-power transport and commutation lemmas with characteristic-two
ring arithmetic. All power maps and their formulas are supplied, and
there is no locality, reducedness, nontriviality or field hypothesis.
The package does not identify the maps with normalized Weyl families,
construct an ambient homomorphism, or prove the G₂ analogue.
