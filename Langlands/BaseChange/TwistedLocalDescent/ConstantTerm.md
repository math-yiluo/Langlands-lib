# Evaluation of the normalized twisted constant term on the ambient radical

Module `Langlands.BaseChange.TwistedLocalDescent.ConstantTerm`. Let `E` be a nonarchimedean local
field, `σ` an automorphism of `E` over a subfield `F` with `E` an `F`-module with the module
topology, `B` a block shape with Levi `M`, parabolic `P`, and `K = GL_n(𝒪_E)`.

The twisted constant term `φ^{P,σ}` of Henniart–Lemaire (2011), II.4.5, p. 86, is the Library's
`normalizedTwistedParabolicConstantTerm E B σ` (module
`Langlands.BaseChange.NormalizedParabolicConstantTerm`). That map integrates over the unipotent
radical `B.unipotentRadical E`, realized as a subgroup of `P(E)`. The local descent works with the
actual radical `B.unipotentSubgroup E` of `GL_n(E)`, on which the Haar measures of
`TwistedLocalDescentStatement` live. This module relates the two.

- `normalizedTwistedParabolicConstantTerm_apply_unipotentSubgroup`: for a Haar measure `μU` on
  `B.unipotentSubgroup E` with `μU(U ∩ K) = 1` and the Haar probability measure `μK` on `K`,

  `φ^{P,σ}(x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du`,

  with `δ_P^{1/2}` the Library's `leviHalfModulus`.

  Proof: the Library's topological group isomorphism `BlockShape.unipotentAmbientEquivContinuous`
  between the two radicals preserves the underlying matrices. So the image `μU'` of `μU` on
  `B.unipotentRadical E` is a Haar measure giving `U ∩ K` volume one. The Library's evaluation
  `normalizedAutParabolicConstantTerm_apply_of_isHaarMeasure` for `μK` and `μU'` gives the formula
  with an integral over `B.unipotentRadical E`. The change of variables along the isomorphism
  (`integral_map_equiv`) turns it into the integral over `B.unipotentSubgroup E`.
