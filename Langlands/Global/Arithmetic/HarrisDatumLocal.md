# Units through continuous isomorphisms of completions with local fields

Worker 84. Helper lemmas in namespace `Langlands.Global.HarrisDatum`, used by
`HarrisDatumCharacterRealizationProof` to compare finite components of a Hecke
character with characters of a local field `K'` (a `PadicField`). Every
result is proved; nothing is assumed.

## Norm one through topological nilpotence

- `tendsto_pow_map`: a continuous ring homomorphism preserves `x^n → 0`.
- `valued_lt_one_iff_tendsto`: in `v.adicCompletion K`, `Valued.v x < 1` iff
  `x^n → 0`.
- `canonicalNorm_lt_one_iff_tendsto`: in `K'`, with the topology of any
  `TopologicalData`, `‖x‖ < 1` iff `x^n → 0` for the canonical (spectral)
  norm, by the Library's `topology_eq_canonicalNormTopology`.
- `canonicalNorm_eq_one_iff` and `valued_eq_one_iff`: for a nonzero
  element, norm (valuation) one iff neither it nor its inverse has norm
  (valuation) less than one.
- `discreteValuation_eq_one_iff`: `T.discreteValuation y = 1` iff the
  canonical norm of `y` is `1`. The proof uses the Library's
  `normalizedAbs_eq_one_iff_discreteValuation` and
  `normalizedAbs_eq_canonicalNorm_pow_degree`.
- `valued_symm_eq_one`: if `φ : v.adicCompletion K ≃+* K'` is continuous, then
  `φ⁻¹` maps norm-one elements to valuation-one elements. Continuity of `φ`
  alone suffices, because both conditions are read through `x^n → 0`.

## Units and unit characters

For a topology `tK` on `K'` equal to `T.topology`, and a continuous `φ`:

- `integralUnit u hu`: the unit of `v.adicCompletionIntegers K` given by
  `φ⁻¹ u`, for a norm-one unit `u` of `K'`. `integralUnit_coe` identifies its
  image in the completion, and `mem_units_of_canonicalNorm` puts `φ⁻¹ u` in
  the integral units.
- `unitCharacter v φ hφ χ₀` is the continuous character `χ₀ ∘ φ` of the
  integral units.
- `finiteComponent_mul_eq`: suppose the finite component of `X` at `v` equals
  `unitCharacter v φ hφ χ₀` on the integral units, and `ψ` is unramified at
  `v`. Then `(X * ψ).finiteComponent v (φ⁻¹ u) = χ₀ u` for every norm-one
  unit `u` of `K'`.
