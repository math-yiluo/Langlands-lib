# Invariant pairings with the Gelfand–Graev representation of `GL_(n+1)`

Internal helper module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`.

- `coefficientMap_evaluationFunctional`: for an intertwiner `Φ` from `π` to the
  `θ`-equivariant functions, the coefficient map of its evaluation functional is `Φ`. This is
  the inverse identity `(functionalEquiv π).apply_symm_apply` from `Whittaker.Algebraic`.
- `deltaPairing : DeltaPairingStatement.{uF, uE}` proves the pairing input of the assembly
  (`DeltaPairingStatement` in `Assembly`) for every universe of the representation carrier.

## Proof of `deltaPairing`

Apply `exists_pairing_intertwiner` (`DeltaPairing`) with the following data:
- `G = GL_(n+1)(F)` with the canonical topology and `N` its upper unipotent subgroup;
- `θ = standardCharacter ψ n`, so `θ⁻¹` is `inverseStandardCharacter ψ n` by definition;
- `ν = μ`, the compatible quotient measure.

The hypotheses come from the Library:
- `SigmaCompactSpace`: `PadicField.TopologicalData.generalLinearSigmaCompactSpace`.
- Group topology: `generalLinearTopologicalGroup`.
- `μ ≠ 0` and right invariance: the `nonzero` and `right_invariant` fields of `IsCompatible`.
- `μ` is finite on compacts: the `regular` field of `IsCompatible`. A regular measure is finite
  on compact sets.
- Compact open subgroups inside every identity neighbourhood:
  `PadicField.TopologicalData.generalLinearCompactOpen`.
- `θ` has open kernel: `isOpen_ker_of_continuous_complex_character`. It uses continuity of
  `standardCharacterContinuous ψ n` and the nonarchimedean structure
  `upperUnipotentNonarchimedean`.

The resulting intertwiner `Φ` gives `ℓ' = evaluationFunctional π Φ ∈ glInverseFunctionals ψ n π`.
By `coefficientMap_evaluationFunctional`, `coefficientMap π ℓ' e` and `Φ e` have the same
underlying function. So the integrand `whittakerProductIntegrand ψ (toWhittaker ψ n x)
(coefficientMap π ℓ' e)` agrees pointwise on `N \ G` with `pairingFun x _`.
