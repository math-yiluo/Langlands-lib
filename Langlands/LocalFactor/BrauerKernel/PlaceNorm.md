# Norms of completions and of norm powers

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. Two small identifications
used when the global characters of Deligne's argument (1973, proof of Lemma 4.12) are read at the
finite places. They are elementary.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Results

- `localUnitNorm_eq_units_map_norm`: for a place `u` of `M` over `z` of `k`, the published local
  norm `FiniteExtension.localUnitNorm z u` is the field norm of `M_u` over `k_z` for the algebra
  structure given by the embedding `completionPadicAlgHom z u` of the canonical packages
  (`Weil.Local.extensionAlgebra`). Both are the norm for the completion map; the proof is `rfl`.
- `normComp_normPower`: for `M / k`, the Hecke character `‖·‖^t ∘ N_{M/k}` of `M` is `‖·‖^t`.
  Proof: on the class of an idele `x`, both sides are `exp (t log |·|)` of the normalized absolute
  value, and `|N_{M/k} x|_k = |x|_M` (the published `full_ideleNorm`).
