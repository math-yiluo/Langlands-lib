# Generator values at the distinguished place of a global realization

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global argument
(1973, proof of Lemma 4.12) the generator values of the local relation at the distinguished place
`v` are compared with the local epsilon factors at `v` of the global characters. This unit writes a
generator value over the bottom field of `F` as a ratio of Tate epsilon factors on the completion
`𝕃_u` of the global generator field, in exactly the form in which those factors occur in the
published finite-place epsilon products (`prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon`):
the additive character is `SystemEpsilon.standaloneTraceCharacter (padicField v) 𝕃_u
(completionPadicAlgHom v u) ψv`, the trace from `𝕃_u` to `k_v` followed by a character `ψv` of `k_v`.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. The setting and notation are those of
`BrauerKernel.RealizationField` and `BrauerKernel.RealizationCharacter`.

## Results

- `embeddingTraceCharacter_comp_symm`: for `p`-adic fields `A`, `F`, `E` in independent universes, a
  `ℚ_p`-isomorphism `φ' : A ≃ F`, an embedding `g : A → E` and a nontrivial character `ψA` of `A`,
  the trace character on `E` of the transport of `ψA` to `F` (`ConductorTransport.additiveCharacter`),
  for the embedding `g ∘ φ'⁻¹`, equals the trace character of `ψA` for `g`. Proof: Mathlib's
  `Algebra.trace_eq_of_equiv_equiv` with `φ'` on the base and the identity on `E` gives
  `Tr_{E/A} x = φ'⁻¹ (Tr_{E/F} x)`.
- `realizationPadicEquiv v φ hφ`: the continuous isomorphism `φ : k_v ≃ F` as an isomorphism of
  `ℚ_p`-algebras (`realization_padicMap`); `realizationPadicEquiv_apply` is its underlying map.
- `generatorValue_eq_realizationEpsilon`: let `g` be a generator over the bottom field with field
  `L ⊆ K`, and `u` a place of `𝕃 = realizationSubfield K θ L` between `v` and `w`. Suppose
  `g.first` and `g.second` are the transports along `σ_g = realizationGeneratorEquiv …` of
  quasicharacters `η₁`, `η₂` of `𝕃_u` (the conclusion of
  `fieldCharacter_eq_realizationTransport`). Let `ψv` be a nontrivial character of `k_v` and `ψb`
  the base character over the bottom field of its transport `ψv ∘ φ⁻¹` to `F`. Then for every Haar
  family and every Haar measure `μ` on `𝕃_u`,

  `generatorValue F ⊥ ψb measures g = ε(η₁, ψv ∘ Tr_{𝕃_u/k_v}, μ, 0) / ε(η₂, ψv ∘ Tr_{𝕃_u/k_v}, μ, 0)`.

  Proof: `generatorValue_eq_epsilon_of_algEquiv` (`BrauerKernel.GeneratorTransport`) applies with
  the embedding `realizationBaseAlgHom v u φ hφ' : F → 𝕃_u` and the isomorphism `σ_g`, which lies
  over `F` by `realizationGeneratorEquiv_base`. That embedding is
  `completionPadicAlgHom v u ∘ φ⁻¹`, so `embeddingTraceCharacter_comp_symm` turns its trace
  character into the standalone trace character of `ψv`.
