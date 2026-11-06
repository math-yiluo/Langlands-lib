# General position from agreement with an auxiliary character

Worker 84. Helper results in namespace `Langlands.Global.HarrisDatum`, used by
`HarrisDatumCharacterRealizationProof`. Every result is proved; nothing is
assumed beyond the stated hypotheses.

- `hasExactUnitNormStabilizer_congr`: `HasExactUnitNormStabilizer L χ` passes
  to any `χ'` that agrees with `χ` on the norm-one elements of `L`. This
  needs two facts: norms from `M` to `L` of norm-one elements have norm one,
  and `F`-automorphisms of `M` preserve the norm. The predicate only evaluates
  the characters at such norms.
- `exists_generalPosition_of_unitAgreement F F'`: there is `χs₀ : FieldCharacter F F'`
  with the following property. For every reciprocity family `e` with
  `NormalizedReciprocity F e`, every `χs : FieldCharacter F F'` that agrees
  with `χs₀` on the units of canonical norm one has
  `IsInGeneralPosition F F' (weilCharacter F e F' χs)`.

The proof of the second result follows the published (private) step
`exactStabilizer_of_auxiliary` of `AuxiliaryGeneralPositionReductionProof`.
It takes `χL` from the published `auxiliaryCharacterFirstOrder` for the
intermediate field `L` of `F'` in `M = galoisClosure F F'`, with exact
unit-norm stabilizer, and sets `χs₀ = χL ∘ (F'ˣ ≅ Lˣ)`. Its two public helpers
on `IntermediateField.restrictAlgEquiv` (continuity and preservation of the
canonical norm) are reused here. Norms of norm-one elements have norm one
because `algebraMap L M (N z)` is the product of the conjugates of `z` over
`L` (`Algebra.norm_eq_prod_automorphisms`). Each conjugate has the norm of
`z`, by Mathlib's `spectralNorm_eq_of_equiv`. The agreement of `χs ∘ a⁻¹`
with `χL` on norm-one elements of `L` therefore gives the exact unit-norm
stabilizer of `χs`. The published `unitNormWeilStabilizerTransport` and
`generalPositionOfExactStabilizer` then give general position.

The identical helper proofs are reused from `Langlands.Global.Arithmetic.AuxiliaryGeneralPositionReductionProof`; their local copies have been removed.
