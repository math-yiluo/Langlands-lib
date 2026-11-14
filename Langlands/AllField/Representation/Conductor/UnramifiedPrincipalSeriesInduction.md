# The unramified principal series as an all-field normalized product induction

Module `Langlands.AllField.Representation.Conductor.UnramifiedPrincipalSeriesInduction`,
namespace `Langlands.AllField.Conductor.UnramifiedPrincipalSeries`.

Let `F` be a field with instances `[ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]` (any characteristic), `ϖ` a uniformizer
(`IsUniformizingElement (ValuativeRel.valuation F) ϖ`) and `q` the residue cardinality
(`IsResidueCardinality q`). The Library defines the normalized unramified principal
series `I(z) = Conductor.UnramifiedPrincipalSeries.principalSeries hϖ n hq z` of
`GL_(n+1)(F)` as smooth induction from the upper triangular group of the character
`b ↦ δ^(1/2)(b) ∏_i χ_{z_i}(b_ii)`, where `χ_z` is the unramified character with
`χ_z(ϖ) = z` and the half modulus is `δ^(1/2)(b) = √q ^ (-∑_i (n - 2i) ord(b_ii))`.
The all-field gamma multiplicativity theorem
`Langlands.AllField.RankinSelberg.gammaMultiplicativity` is instead about the all-field
normalized product induction `(⟨⟩ : LocalFieldData F).normalizedProductInduced B σ` of
representations `σ_i` of the diagonal blocks of a block shape `B`. This module identifies
the two: `I(z)` is equivalent to the normalized product induction of the rank-one
characters `χ_{z_0}, …, χ_{z_n}` (as representations `g ↦ χ_{z_i}(det g)` of `GL_1(F)` on `ℂ`)
from the parabolic of `n + 1` blocks of size one.

This is an internal bridge between two Library definitions of the same induced
representation; it has no separate literature counterpart. In JPSS 1983 (section (3.1),
printed pages 404–405), and in the Markdown of the target statement
`Langlands.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement`, the
principal series is by definition the induced representation of a family of
characters.

## Declarations

- `sum_pairs_sub_eq`: `∑_(i<j) (λ_i - λ_j) = ∑_i (n - 2i) λ_i` for `λ : Fin (n + 1) → ℤ`.
  Proof: swap the double sum of the `λ_j`; the index `i` has `n - i` successors and `j`
  has `j` predecessors.
- `prod_zpow_eq_zpow_sum'`: `∏_(i ∈ s) x ^ f i = x ^ (∑_(i ∈ s) f i)` for real `x ≠ 0`
  and integer exponents, by induction on `s`.
- `borelBlocks n` (abbrev): the block shape `RankinSelberg.succBlockShape (fun _ => 0) _`
  of `n + 1` blocks of size one, written in the form used by the multiplicativity
  statement. `borelBlocks_eq_singletons`: it is `BlockShape.singletons (n + 1)`
  (by `rfl`).
- `ord_ofInstances`: for a unit `a`, the order of `a` for the ambient data
  `LocalFieldData.ofInstances F` equals `ord hϖ a`, the exponent with
  `v(a) = v(ϖ)^(ord hϖ a)`. Proof: the discrete valuations of `a` and `ϖ^(ord hϖ a)`
  agree, and `ϖ` has discrete valuation `exp (-1)`
  (`AllField.RankinSelberg.discreteValuation_of_isUniformizingElement`).
- `normalizedAbs_units`: on units, the normalized absolute value of the ambient data is
  `q ^ (-ord hϖ a)`, by `ord_ofInstances` and
  `AllField.RankinSelberg.residueCardinality_ofInstances`.
- `continuous_character`, `quasicharacter`, `quasicharacter_toMonoidHom`: `χ_z` is
  continuous (its kernel is open, `isOpen_ker_character`), so it defines a
  `HarmonicAnalysis.Quasicharacter F`, whose underlying homomorphism is `χ_z`.
- `mem_borelBlocks_parabolic_iff`, `borelBlocks_parabolic_le`,
  `upperTriangular_le_borelBlocks_parabolic`: the parabolic subgroup of `borelBlocks n`
  is the upper triangular group (`BlockShape.singletons_mem_parabolic_iff`).
- `determinant_leviProjection`: the determinant of the `i`-th (`1 × 1`) Levi block of an
  element `b` of this parabolic is the diagonal entry `b_ii`.
- `leviModulus_borelBlocks`: the all-field block modulus
  `∏_(i<j) |det b_i| / |det b_j|` of `b` equals `q ^ (-∑_i (n - 2i) ord(b_ii))`. Proof: each
  block determinant has normalized absolute value `q ^ (-ord(b_ii))`; combine the
  powers and apply `sum_pairs_sub_eq`.
- `parabolicHalfModulus_borelBlocks`: consequently the all-field positive half modulus
  (the square root of the block modulus) equals `halfModulusCharacter hϖ n hq b`, the
  half modulus of `principalSeries`, since `√(q ^ E) = √q ^ E`.
- `blocks n z` (abbrev): the family `i ↦ RankinSelberg.rankOneCharacter (character hϖ (z i))`
  of rank-one representations; `blocks_apply` evaluates it.
- `constantBaseRingEquiv_blockTensor`: under the identification
  `PiTensorProduct.constantBaseRingEquiv` of `⨂_(i : Fin (n+1)) ℂ` with `ℂ` (product of the
  entries), the block tensor representation of `blocks n z` at a Levi element `L` is
  multiplication by `∏_i χ_{z_i}(det L_i)`. Proof: induction on the tensor.
- `parabolicCharacter` (abbrev): the normalized Borel character `normalizedCharacter`
  of `I(z)`, restricted to the parabolic of `borelBlocks n`.
- `inducingEquiv` (def): an equivalence, given by `constantBaseRingEquiv`, between the
  inducing representation of the all-field normalized product induction (the half
  modulus times the block tensor of `blocks n z`, composed with the Levi projection) and
  the one-dimensional representation of `parabolicCharacter`. The intertwining property
  is `constantBaseRingEquiv_blockTensor`, `parabolicHalfModulus_borelBlocks` and
  `determinant_leviProjection`.
- `principalSeriesEquiv` (def): `(principalSeries hϖ n hq z).Equiv
  ((⟨⟩ : LocalFieldData F).normalizedProductInduced (borelBlocks n) (blocks hϖ n z))`.
  Both sides are smooth induction by right translation. The first step,
  `Induction.comapSmoothInducedEquiv` along the identity of `GL_(n+1)(F)`, replaces the
  upper triangular group by the equal parabolic of `borelBlocks n`. The second step is
  `Induction.smoothInducedEquiv` applied to `inducingEquiv` (inverted).
