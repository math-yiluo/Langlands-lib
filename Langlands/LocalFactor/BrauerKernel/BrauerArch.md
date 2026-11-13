# The archimedean block of the Brauer product package

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, proof of Lemma 4.12) the archimedean factors of the product of Hecke L-functions
cancel, because all archimedean components are powers of the absolute value and the types are
balanced. This unit carries out that cancellation for the archimedean block of the published
package `RelativeWeilEngine.hasGlobalEquation_brauerProduct`, with exponent `0` on the base
character.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Setting

- `E/k` is a totally real extension of number fields.
- `K : Fin n → IntermediateField k E` are intermediate fields with weights `r i`.
- `Λ₁ i`, `Λ₂ i` are Hecke characters of `K i` whose archimedean components are those of
  `‖·‖^{t₁ i}` and `‖·‖^{t₂ i}`.
- The data for each `Λ_j i` is `normPowerArchData` (unit `ArchimedeanData`), for an additive
  character `ψ` of `A_k` with real components `a`.
- The balancing hypothesis `hdim` reads, for every `τ : ℂ`,
  `Σ_i r_i [K i : k] ([t₁ i = τ] - [t₂ i = τ]) = 0`.

## Results

- `isTotallyReal_intermediateField`: an intermediate field of a totally real field is totally
  real (Mathlib's `IsTotallyReal.of_algebra`). It is used as a local instance.
- `meromorphicEq_brauerArch_A`: the archimedean L-function block
  `A_F(s)^0 · Π_i (A_{1,i}(s) / A_{2,i}(s))^{r_i}` has the punctured germ of `1`. Proof:
  `normPowerArchData_A` writes each factor as a power `[K i : k]` of a product over the real
  places of `k`. `meromorphicEq_prod_baseRealDenominator` then applies.
- `meromorphicEq_brauerArch_Ad`: the same for the dual block, which carries the exponents
  `-t_j i`. The balancing hypothesis for `-t` is `hdim` at `-τ`.
- `brauerArch_Ae_eq_one`: the archimedean epsilon block is `1` at every `s`
  (`normPowerArchData_Ae` and `prod_baseRealEpsilon_eq_one`).
