# Joint measurability of norm-one Arthur truncation

`Langlands.Global.ArthurTruncation.NormOneTruncationImaginaryFamilyMeasurabilityStatement`
gives the joint measurability clause for a compact set `C ⊆ ℝⁿ` of imaginary parameters
and a fixed truncation parameter `Tp`. Its conclusion uses restricted Lebesgue measure
on `C` times the quotient of the supplied Haar measure on `G(𝔸)¹`. The theorem
`aestronglyMeasurable_normOneTruncation_imaginary_family` proves this statement.

For each `g ∈ G(𝔸)¹`, the spectral function `λ ↦ E(λ)(g)` is scalar meromorphic in linear
coordinates with holomorphy domain `DE`. Every `i e(x)` for `x ∈ C` belongs to `DE`.
For each `x ∈ C`, the group slice `g ↦ E(i e(x))(g)` on `G(𝔸)¹` is Borel measurable
and pointwise left `G(F)`-invariant. The measurable group slices and their invariance
are explicit inputs to the specialization.

## Provenance

The proof uses the constant-term integral and the parabolic coset sums in Arthur's
truncation formula (13.1) over `ℚ` on the norm-one quotient and in Lapid's number-field
version. It derives the family assertion for the Library's pointwise `normOneTruncation`.
Lapid's Working hypothesis concerns holomorphic families of cleared series taking values
in a space of smooth functions on the rational quotient. Here the spectral continuity
comes from the supplied scalar holomorphy, and the group regularity used in the proof
is precisely Borel measurability and rational invariance of the slices.

- J. Arthur, *An introduction to the trace formula* (2005), §13, formula (13.1),
  printed p. 68 (PDF p. 80), in `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*
  (2011), §2, Working hypothesis and truncation formula, printed p. 312 (PDF p. 321),
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`.

## Proof

`measurable_normOneTruncation_family` starts with a jointly measurable family on
`X × G(𝔸)¹` for a measurable parameter space `X`. The zero extensions to `G(𝔸)` are
jointly measurable since the norm-one subgroup is closed. They are left rational-invariant
because the rational subgroup is contained in the norm-one subgroup.

For each standard parabolic, multiplication gives a jointly measurable integrand on
`X × G(𝔸) × N(𝔸)`. Rational invariance makes it constant on the left `N(F)`-cosets
in the last variable. `LeftCosetSpace.measurable_out_of_invariant_prod` descends that
integrand by using a measurable section of the discrete quotient. Its evaluations agree
pointwise with evaluation at `Quotient.out` by invariance. Integration against the
normalized probability measure on `N(F) \ N(𝔸)` preserves measurability of the constant
term. The cutoff is the indicator of finitely many strict inequalities of continuous
weight-height functions. The rational coset sums are countable and the outer sum is
finite, so truncation preserves joint measurability. Rational invariance of the truncated
functions (`Idempotence.truncation_rational_mul`) allows the same measurable-section argument
on `G(F) \ G(𝔸)¹`.

`aestronglyMeasurable_normOneTruncation_on_compact` uses `X = C` with its subtype
measurable space. It extends the measurable quotient function to `ℝⁿ × G(F) \ G(𝔸)¹`
using the measurable embedding of `C × (G(F) \ G(𝔸)¹)`. The product of restricted
Lebesgue and the quotient measure is supported on this set, so the extension agrees
almost everywhere with the stated truncation.

For imaginary parameters, the map `x ↦ i e(x)` in any complex linear chart is
real-linear and continuous. Holomorphy on `DE` then gives continuity of the spectral
slices on the subtype `C`. With the measurable group slices, Mathlib's
`measurable_uncurry_of_continuous_of_measurable` gives the jointly measurable evaluation
used by the compact-parameter lemma.
