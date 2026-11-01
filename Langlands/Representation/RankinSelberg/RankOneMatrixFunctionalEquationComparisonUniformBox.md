# Uniform box extraction at arbitrary additive conductor

This internal prerequisite extends the published comparison-box computation
from an individual model vector to every continuous coefficient fixed by one
principal congruence subgroup. The additive character has arbitrary conductor.
The final matrix-to-rank-one gamma comparison remains outside this module.

Fix a canonical p-adic field `F`, a unitary additive character `ψ`, and an
ambient group `GL_(m+2)`. Write `c` for the additive conductor of `ψ`.
For a positive integer `a` with `c + a ≥ 0`, use the actual published matrix test

`Φ = boxLatticeTest F (c + a) c a`.

Thus the `(0,0)` entry lies in the additive lattice of level `c + a`,
the other first-row entries lie in the lattice of level `c`, and each remaining
entry differs from the corresponding identity entry by an element of
`levelSet F.Carrier a`. The test is defined on the full matrix space.

The definition `boxExtractionConstant` reuses `boxComparisonVolume` with an
implicit rank argument. It is the product of three real volumes:
the box support in the integral general linear group, the torus box, and the
unipotent box. For `A ≥ 0` and `a > 0`,
`boxExtractionConstant_pos` proves that this product is strictly positive.
It depends on the rank and the box, not on the coefficient.

The theorem `uniform_box_extraction` applies to every continuous function
`H : GL_(m+2)(F) → ℂ` satisfying

* `H(u h) = standardCharacter ψ (m+1) u * H(h)` for the actual upper
  unipotent subgroup;
* `H(h y) = H(h)` for every `y` in the principal subgroup of level `a`.

It proves equivalence of genuine Bochner integrability of `Φ(h) H(h)`
against the existing full general linear Haar measure and of
`H(rankOneEmbedding m g)` against the existing weighted scalar measure
`glOneMeasure F (m+1)`. It also proves equality of the former integral with
`boxExtractionConstant F (c+a) c a` times the latter. The displayed integral
identity uses Lean's totalized integrals: when either function is not
integrable, the equivalence proves that both integrals are zero by definition.
The convergence equivalence is a separate part of the conclusion.

The implemented proof has the following steps.

* `mul_mem_box_of_le` and `mul_mem_box_iff_of_le` generalize the published
  multiplication calculation to `q ≤ A`; the older restrictions `q ≤ 0`
  and `A ≥ 0` are not needed for that calculation. The principal first row
  has exactly the required level when `A = q + a`.
* `unipotentBox_eq_entry_preimage` identifies the unipotent box with a finite
  product of compact lattices through the actual strict upper-entry
  homeomorphism. Hence its Haar volume is finite for every integer `q`,
  including positive values.
* `cutoffUnipotent_mem_principalLevel` places a small transvection in the
  principal subgroup. Equivariance and right invariance force
  `ψ(det(g) x) = 1` for every `x` of level `a`, whenever the scalar restriction
  of `H` is nonzero. The published lattice-annihilator theorem then gives
  scalar support in level `c + a`, uniformly in `H`.
* `boxCoefficient_point` computes the coefficient at the actual Iwasawa
  parametrization point. It is the scalar restriction of `H` multiplied
  by the torus and unipotent indicators. Character triviality follows from
  the conductor and `-a ≤ c`.
* `boxCoefficient_extraction_of_principalLevel` uses the published integral
  support and parameter-product formulas. The exact nonnegative integral
  of the norm factors into the three positive finite volumes and the norm
  integral of the scalar restriction. This proves both directions of
  absolute convergence. The Bochner formulas give the stated value.

The more general extraction theorem keeps the lattice levels and the scalar
support hypothesis explicit. The final theorem supplies them automatically
from `c` and `a`. No representation, irreducibility, chosen model vector,
self-dual additive Haar normalization, or functional equation is assumed.
This module does not construct a universal compact averaging measure for
functions without the stated right principal-level invariance.

The provenance is derived: the implementation extends
`RankOneMatrixWhittakerComparisonBox`, uses the actual lattice test and the
level/lattice identification from
`RankOneMatrixFunctionalEquationComparisonBoxFourier`, and applies the published
`UpperUnipotentEntryCoordinates` homeomorphism and the canonical
lattice-annihilator theorem. These existing definitions and proofs, together
with standard finite-product compactness and Bochner/Lebesgue integration,
are the mathematical inputs.
