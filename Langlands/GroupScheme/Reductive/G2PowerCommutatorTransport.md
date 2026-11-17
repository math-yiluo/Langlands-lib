# The characteristic-three G₂ commutator power calculation

This internal derived package performs the exceptional unequal-power
G₂ calculation on supplied actual maps from `Ga R` to a group scheme.
It uses the literal convention
`CommRel u v L : (u(x)v(y))⁻¹(v(y)u(x)) = product(L)`.
No root-group or Weyl-conjugation identifications are encoded
implicitly.

Let the target short-long formula be

`CommRel C A
 [(P₁,1,1,1), (P₂,1,2,1), (P₃,-1,3,1), (P₄,-1,3,2)]`.

Let `F`, `F₃` be supplied actual homomorphisms of the additive line with
all-test point formulas `x ↦ x^q` and `x ↦ x^(3q)`, and assume
explicitly that `q` is odd. In the intended application `q` is a
power of three. The definition `g2UnequalPowerTerms` annotates the
reversed target list with these term powers and its new coefficients
and degrees.

`g2_unequal_power_commRel_reversed` verifies the exact coefficient
and exponent balances, giving output order
`P₄_(3q), P₃_(3q), P₂_q, P₁_q`. Oddness supplies
`(-1)^q = -1`; no unstated sign identity is used.

In a base ring with `3 = 0`, the supplied target relation
`CommRel P₁ P₂ [(P₄,-3,1,1)]` makes `P₁` and `P₂` commute.
With the additional explicit premise `PointsCommute P₃ P₄`,
`g2_unequal_power_commRel` swaps the two adjacent pairs and proves

`CommRel (F₃ ≫ A) (F ≫ C)
 [(F₃ ≫ P₃,1,1,1), (F₃ ≫ P₄,1,2,1),
  (F ≫ P₁,-1,3,1), (F ≫ P₂,-1,3,2)]`.

The mixed formulas are handled separately.
`g2_mixed_long_power_commRel` uses the target relation
`CommRel A P₃ [(P₄,-1,1,1)]` to produce
the powered relation with coefficient two and two additional
vanishing coefficient-minus-three terms.
`g2_mixed_short_power_commRel` uses the target three-term relation
`CommRel C P₁ [(P₂,2,1,1),(P₃,-3,2,1),(P₄,-3,1,2)]`
to obtain the powered singleton relation with coefficient minus one.
Both use `2 = -1` and `-3 = 0` in `R`.
`g2_mixed_zero_power_commRel` gives any remaining singleton
coefficient-minus-three source mixed relation when the needed
target commutation is explicitly supplied.

The provenance is literal reversal, the imported balanced-power and
integer-coefficient common-power transports, and the explicit
characteristic-three coefficient and commutation checks. Every map,
point formula, target relation and required target commutation is
retained. There is no locality, reducedness, nontriviality or field
hypothesis, and the package does not construct or identify a
normalized root family or an ambient group homomorphism.
