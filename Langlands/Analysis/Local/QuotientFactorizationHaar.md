# Complementary-subgroup Haar normalization from compact open masses

This is an internal deduction from the actual quotient chart, compatible Weil
measure, compact-open orbit restriction and regular Haar uniqueness. Its
application is the normalized complementary-unipotent integration in
Waldspurger (2003), IV.1, printed p.279 (PDF p.45), and the composition
assertion IV.1(12), printed p.283 (PDF p.49).

Let `H` and `K` be subgroups of a topological group `G`. Supply a
homeomorphism `m : H × K ≃ₜ G` given by the literal multiplication
`m(h,k) = h*k`. The actual quotient chart
`c : K ≃ₜ LeftQuotient H` is `factorQuotientHomeomorph` from
`QuotientFactorization`. No normality or commutation hypothesis is used.
The definition `factorQuotientMeasure H K m hm μK` constructs the measure
on this actual quotient by pushing `μK` forward through `c`. The
comparison below proves equality with a supplied compatible Weil measure.

`factorQuotientHomeomorph_mul` proves that `c(k*l)` is the right translate
of `c(k)` by `l`. Thus
`isMulRightInvariant_map_factorQuotientHomeomorph_symm` pulls any
right-invariant quotient measure back to a right-invariant measure on `K`.
It compares the two composites with `c.symm` and uses composition of
measure pushforwards.

Assume `G` is locally compact. Supply Borel
structures on `K` and the actual quotient, a regular quotient measure `ν`,
and a regular two-sided Haar measure `μK` on `K`.
`exists_smul_map_factorQuotientHomeomorph_symm` proves
`Measure.map c.symm ν = a • μK` for a nonnegative real scalar `a`.
Local compactness of `K` is derived from its homeomorphism with the actual
quotient. The pullback is regular and right invariant. Its inverse measure
is left invariant, and `μK.inv` is a regular left Haar measure. Haar
uniqueness compares these inverse measures; applying inversion again gives
the displayed comparison. No nonzero premise on `ν` is needed for this
scalar comparison.

For exact normalization, also assume `G` is Hausdorff and `H` is closed.
Supply Borel structures on `G` and `H`,
regular Haar measures `μG`, `μH`, right invariance of `μH`, and
`IsCompatible H μG μH ν`. Let `S` be a compact open subgroup of `G`
and `B` a compact open subgroup of `K`. The two additional inputs are

- the set identity `c '' B = leftQuotientMap H '' S`;
- the local normalization
  `μG S = μH {h : H | h.val ∈ S} * μK B`.

`IsCompatible.measurePreserving_factorQuotientHomeomorph_of_compactOpen`
derives exact preservation of `μK` by `c`. Testing the published
`IsCompatible.integral_compactOpenOrbit` formula with the constant
function one gives
`μH(H ∩ S) * ν(leftQuotientMap H '' S) = μG S`.
The compact intersection and compact quotient orbit have finite mass.
Equality of their real masses therefore gives the displayed identity
of extended nonnegative masses. The intersection mass is positive, so
cancellation against the local normalization gives equality of the
orbit mass and `μK B`. The two inputs therefore
give `Measure.map c.symm ν B = μK B`. Since `μK B` is finite and
positive, the scalar comparison forces `a = 1`. Pushing forward by `c`
finishes the proof. This uses the compact-open integral formula directly and does
not require second countability.
`IsCompatible.factorQuotientMeasure_eq_of_compactOpen` records the resulting
equality of the constructed measure and `ν`.

`IsCompatible.measurePreserving_factorProduct` proves the converse
normalization direction: exact measure preservation by `c` implies exact
measure preservation by `m`. Here the product measurable structure on
`H × K` must be its Borel structure, `μH` and `μK` are S-finite, and
their product measure is regular. These are explicit premises. For a
real continuous compactly supported test on `G`, its pullback by `m`
is compactly supported and integrable for the regular product measure.
Scalar Fubini identifies its product integral with the integral over `K`
of the subgroup average. The exact chart comparison and the real Weil
formula identify that integral with the supplied ambient integral.
Regular-measure extensionality proves equality of measures.

`IsCompatible.measurePreserving_factorProduct_of_compactOpen` combines
these results. Thus a literal subgroup product, the displayed local
compact-open set identity and local normalization determine the full
ambient product-measure equation. The full product identity is a
conclusion.

For the reductive application, the actual complementary product
homeomorphism, the compatible quotient measure, the stated compact-open
factorization and mass normalization, and all measurable-structure,
regularity and S-finiteness premises remain to be supplied. This
deduction does not prove the root-distance factorization, analytic
convergence, rational continuation or Plancherel, and its local
normalization inputs may not be installed as permanent structural
assumptions for whole-program completion.
