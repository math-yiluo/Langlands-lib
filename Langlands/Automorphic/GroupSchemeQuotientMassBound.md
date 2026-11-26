# Conjugate subgroup mass bounds for continuous functions on the positive quotient

Module `Langlands.Automorphic.GroupSchemeQuotientMassBound`. For an affine group scheme `G`
of finite type over a number field `F` and the positive-central rational quotient
`Q = H \ G(𝔸_F)`, with `H = positiveRationalSubgroup F G T i` and its Haar measure
`μH = positiveRationalSubgroupHaarMeasure`, the module packages pointwise bounds of the form
`‖h(H x)‖² ≤ C · μH(H ∩ x S x⁻¹)`. These bounds come from compact convolution and survive
further averaging.

## Definitions

- `conjugateMass F G T i hi I e hc S x`: the real number `μH(H ∩ x S x⁻¹)`, written as the
  measure of the preimage under `Subtype.val` of the image of `S` under `s ↦ x s x⁻¹`.
- `QuotientMassBound F G T i hi I e hc h S C`: for every adelic point `x`,
  `‖h(LeftCosetSpace.mk H x)‖² ≤ C · conjugateMass … S x`.

## Results

- `conjugateMass_ne_top`: for compact `S` the conjugate mass is finite. `H` is closed
  (`isClosed_positiveRationalSubgroup`), so the preimage of the compact set `x S x⁻¹` in `H` is
  compact, and the Haar measure `μH` is finite on compacts.
- `conjugateMass_le_of_subset`: if `y S y⁻¹ ⊆ x S' x⁻¹` with `S'` compact, then the mass for
  `(S, y)` is at most the mass for `(S', x)`.
- `isCompact_conjugateSet`: `B S B⁻¹` is compact for compact `B` and `S`.
- `quotientMassBound_weightedQuotientOrbitIntegral`: **stability under weighted orbit
  integrals.** Let `h` satisfy the mass bound for a compact `S` and `C ≥ 0`. Let `b` be a
  continuous parameter map `Y → G(𝔸_F)` and `w` a compactly supported continuous weight. Then
  the Library's `weightedQuotientOrbitIntegral` `q ↦ ∫ w(y) h(q · b(y)) dν(y)` satisfies the
  mass bound for `B S B⁻¹`, where `B = b(supp w)`, with constant `C (∫ ‖w‖ dν)²`. For `y` in the
  support of `w`, `(x b(y)) S (x b(y))⁻¹ ⊆ x (B S B⁻¹) x⁻¹`, so each value `h(H x b(y))` is at
  most `√(C m)`, with `m` the mass of `x (B S B⁻¹) x⁻¹`. Integrating against `‖w‖` and squaring
  gives the bound.
- `exists_quotientMassBound_representative`: this theorem takes
  `GroupSchemeQuotientL2ContinuousRepresentativeStatement` as a hypothesis. From it, for every
  compactly supported continuous weight `f` on `G(𝔸_F)` and every class `φ`, the class
  `haarQuotientL2IntegratedAction … f φ` has a continuous representative. That representative
  satisfies the mass bound for `supp f · (supp f)⁻¹`, with constant `M ∫ ‖f‖ ‖φ‖²`, where `M`
  bounds `‖f‖`. The argument is the one of `generalLinearContinuousSmoothingGrowth`.
- `QuotientMassBound.sliceGrowth`: for `G = GL_n`, a mass bound for a compact set gives, on
  every finite slice, a bound by a constant times
  `infiniteAdelicHilbertNorm F n a ^ finrank ℝ (ArchimedeanMatrix F n)`. This is the Library's
  `generalLinear_sliceGrowth_of_compactConjugateBound`.

## Provenance

The pointwise bound by the subgroup mass of `x S x⁻¹` is the estimate of
`GroupSchemeQuotientL2ContinuousRepresentativeStatement`. The Library obtains it from its
general quotient convolution theorem. It is related to, but different from, the estimate (9.13)
of Getz and Hahn, *An Introduction to Automorphic Representations* (2024), printed pp. 247–248
(PDF pp. 259–260). There (9.13) is the uniform bound `‖R(f)φ‖_∞ ≪_f ‖φ‖₂`, assumed for all `φ`
in a closed invariant subspace in the trace-class criterion of Lemma 9.3.3. The bound here
depends on the coset through the subgroup mass. Its stability under further compactly supported
averaging is an internal consequence. The Library uses it to obtain growth on each finite slice
for the smoothed forms of `Langlands.Automorphic.GeneralLinearSummandFormsNonzero`. The book
does not argue this way. The module does not prove the continuous-representative statement;
`exists_quotientMassBound_representative` assumes it.
