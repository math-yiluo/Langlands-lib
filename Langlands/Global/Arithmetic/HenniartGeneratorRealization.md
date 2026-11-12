# Induced generators above `W_{F'}` in the Weil image of witnessed pairs

Author: Worker 5134. Module `Langlands.Global.Arithmetic.HenniartGeneratorRealization`
(namespace `Langlands.Global`). It is a helper for the reduction
`HenniartGlobalizationReductionStatement`
(`Langlands.Global.Arithmetic.HenniartGlobalizationReduction`) of
`HenniartGlobalizationStatement` (Henniart 2000, §3.4). It contains no definitions.

Notation: `K : PadicField p`; `F'` a finite extension of `K`; `F₀` a CM number field with
compact adele quotient; `(E', Lg, K₀, P, Ps, φ, φs, θ)` a paired-place configuration for
`F'` in the sense of `Harris.IsPairedPlaceConfiguration` (Library,
`Global/Arithmetic/HarrisDatum*.lean`). Its main place `P.v` of `F₀` carries a ring
isomorphism `P.iso : F₀_{P.v} ≅ K`, and its place `P.v'` of `E'` carries
`φ : E'_{P.v'} ≅ F'`. `W_X` denotes the local Weil group of a p-adic field `X`, and
`weilSubgroup X L` is `W_L ⊆ W_X`.

## Results

- `discreteValuation_eq_one_of_valued_eq_one F' u φ hφs ha`: if `φ : E'_u ≃+* F'` has
  continuous inverse and `a ∈ E'_u` has valuation `1`, then `φ a` has normalized discrete
  valuation `1` in `F'`. Proof: valuation `1` means that neither `a^n → 0` nor
  `a^{-n} → 0` (`HarrisDatum.valued_eq_one_iff`, `valued_lt_one_iff_tendsto`). The same
  holds for the canonical norm on `F'` (`canonicalNorm_eq_one_iff`,
  `canonicalNorm_lt_one_iff_tendsto`). Convergence transfers back along the continuous
  map `φ⁻¹` (`HarrisDatum.tendsto_pow_map`).

- `exists_weilImage_realizeExact_continuousInduce hHarris hccre hlrm hlir hcalip hacc hasi
  htransfer hc K F' K₀ P Ps φ φs θ hconf h f hf L hL η hη` (Henniart 2000, §3.4, for one
  generator). Data: `h : residuePrime P.v = p`; a `ℚ_p`-algebra isomorphism
  `f : K ≅ F₀_{P.v}` with `f⁻¹ = P.iso` (`hf`); a Galois extension `𝔼/F₀` containing `E'`
  (as a tower `F₀ ⊆ E' ⊆ 𝔼`); a finite extension `L` of `F₀_{P.v}` such that
  `T y ∈ W_L ↔ y ∈ W_{F'}` for `T := completionWeilTransport P.v h K f` (`hL`); a
  continuous character `η` of `W_L` with `|η| = 1`. Conclusion: some `y` in
  `weilImage F₀ 𝔼 c P.v` satisfies
  `realizeExact (includeUnitary y) = Ind_{W_L}^{W_{F₀,P.v}} [η]`.

  Hypotheses: `Harris.Proposition48Statement` (Harris 1998, Proposition 4.8),
  `LocalClassField.CommonClosureReciprocityExistence` (for the normalized reciprocity
  family `e` on `K` that Harris's proposition needs), and the six propositions listed in
  module `HenniartInducedGenerator`.

  Proof.

  1. The configuration gives `P.v'` as the only place of `E'` above `P.v`
     (`Harris.finitePlacesAbove_subsingleton`), continuity of `φ⁻¹`, and the
     compatibility of `φ` with `P.iso` on `F₀_{P.v}`. With `hf` this is the hypothesis of
     `exists_conj_completionWeilMap_range` (module `HenniartCompletionConjugation`),
     which gives `g` with `y ∈ range (completionWeilMap P.v P.v') ↔ g y g⁻¹ ∈ W_L`.
  2. `continuousInduce_characterClass_eq_along_conj` (module
     `Langlands.VirtualRepresentation.ExactInductionConjugation`) rewrites
     `Ind_{W_L}[η]` as `Ind_{completionWeilMap P.v P.v'} [η']` with
     `η' := η ∘ conjCodRestrict …`, a modulus-one character of `W_{E'_{P.v'}}`.
  3. Let `eu` be the geometric reciprocity candidate of `E'_{P.v'}` (published
     `geometricWeilReciprocityExistenceUniqueness`). Transport the field character
     `fieldCharacter eu η'` of `E'_{P.v'}ˣ` along `φ⁻¹` to a character `χ₀` of `F'ˣ`.
  4. With `e` from `hccre`, the published `harrisDatumCharacterRealization` gives Hecke
     characters `χ, χs` and `ξ` of `E'` forming a Harris datum, with `χ = χ₀` on the
     units of `F'`. Harris's Proposition 4.8 (`hHarris`) gives a cuspidal class `π` that is
     a weak automorphic induction of `ξ`. The datum also gives regularity of `ξ`,
     `ξ⁻¹ = ξ ∘ c`, and the component identity `ξ_{P.v'}(a) = χ(φ a)`.
  5. `ξ` is unitary (`isUnitary_of_isConjugateInverse`). On units of `E'_{P.v'}`,
     `ξ_{P.v'}` equals `fieldCharacter eu η'`: by step 4 and the first result,
     `ξ_{P.v'}(a) = χ(φ a) = χ₀(φ a) = fieldCharacter eu η' (a)`.
     `exists_weilCharacter_eq_mul_unramified` (module `HenniartLocalCharacter`) gives `z`
     with `|z| = 1` and `weilCharacter eu ξ_{P.v'} = η' · (z_unr ∘ completionWeilMap)`.
  6. `exists_witnessedGenerator_inducedReciprocity` (module `HenniartInducedGenerator`),
     applied with `L := 𝔼` and twist `z⁻¹`, gives a witnessed generator `d`. Its Weil
     element realizes
     `z⁻¹_unr ⊗ Ind [weilCharacter eu ξ_{P.v'}]`. The projection formula
     `continuousTwist_continuousInduceAlong` and `continuousTwist_characterClass` turn this
     into `Ind [(z⁻¹_unr ∘ cWM) · η' · (z_unr ∘ cWM)] = Ind [η']`. Step 2 identifies this
     with `Ind_{W_L}[η]`, and `y := d.weilElement ∈ weilImage` (`witnessed_weil_mem`).

## Provenance

Internal helper for Henniart (2000), §3.4. Henniart starts from a character of `F'ˣ`
that he globalizes to a Hecke character `ξ` with prescribed local component (Harris's
datum, made explicit in the Library). He applies Harris (1998), Proposition 4.8 and then
reads off the local component at `v` of the resulting Weil-group representation. This
module carries out these steps for one Brauer generator `Ind_{W_L} η`. The conjugation
step and the unramified twist are bookkeeping that the Library's choices of embeddings
and normalizations require.
