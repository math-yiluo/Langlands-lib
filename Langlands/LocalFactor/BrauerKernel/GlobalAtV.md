# The epsilon product at the distinguished place and the generator values

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, proof of Lemma 4.12) the given p-adic field `F` and its Galois extension `K` are
realized as completions `k_v` and `K'_w` of a Galois extension of number fields. The local
epsilon product at `v` is then the product of the abelian epsilon ratios of the presentation.
This unit makes that identification.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Results

- `evaluationMap_eq_zero_of_prod`: the evaluation of a presentation `z` is `0` when the product
  `Π_i generatorValue(g_i)^{z(g_i)}` over an enumeration `gs` of the support is `1`. Proof:
  `toMul` of the evaluation is this product (`Finsupp.linearCombination_apply`, `toMul_sum`,
  `toMul_zsmul`).
- `eq_under_of_unique`: if `w` is the only place of `K'` above `v`, then every place above `v`
  of an intermediate field `M` is the place `w.under` under `w`. Proof: choose a place of `K'`
  above it (`placeAbove`). It lies over `v` (`Ideal.LiesOver.trans`), hence equals `w`.
- `under_liesOver`: the place under `w` lies over `v` (`Ideal.LiesOver.tower_bot`).
- `evaluationMap_eq_zero_of_placeEpsilon`. Setting: a realization of `D.K / F` (with
  `F : PadicField (residuePrime v)`) as the completion at the only place `w` above `v` of a
  Galois extension `K'/k`, with the data `φ, ψ, θ` and their compatibilities.

  Hypotheses: `hM`, `hN3` (`LocalTransferReciprocityStatement`) and `hCC`; Hecke characters
  `Θ_j g` whose reciprocity characters are the inflated characters of `D.θ_j g`; a Hecke
  character `α` with `α_v = 1`; and `hplace`, saying that `placeEpsilonRatioProduct` of the place
  `v` for the characters `(α ∘ N) · ‖·‖^{t_j g} · Θ_j g` is `1`.

  Conclusion: `evaluationMap F _ ψb measures z = 0`, for every Haar family and the base
  character `ψb` of the transport of `ψv` along `φ`.

  Proof: by the previous item it suffices to show the product of generator values is `1`. Split
  the place product over the generators (`Fintype.prod_sigma`). Each fibre has the single place
  `u` under `w` (`eq_under_of_unique`). At `u`:
  1. `hM` and `hN3` give a local map `ι` (unit `LocalMapTransport`), with a normalized family at
     `u` from `hCC`.
  2. `fieldCharacter_eq_realizationTransport` (unit `RealizationCharacter`) identifies the two
     characters of the generator with the transports of the components at `u`. Its Galois
     hypothesis comes from `globalCharacter_apply` (unit `GlobalCharacters`).
  3. `generatorValue_eq_realizationEpsilon` (unit `RealizationEpsilon`) identifies the generator
     value with the epsilon ratio at `u`.
