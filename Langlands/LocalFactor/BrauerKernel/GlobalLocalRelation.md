# Local relations at every finite place from a global relation

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, proof of Lemma 4.12) a relation among induced characters of the global Weil
group is restricted to the local Weil group at each finite place. This gives the local relations
that make the local L-factors and the local epsilon products cancel. This unit performs that
restriction at every finite place, using two published statements as hypotheses. Both are proved
in the Library: `LocalRelativeWeilMapExistenceStatement` by `localRelativeWeilMapExistence` and
`LocalClassField.ExtensionWeilTransferReciprocityStatement` by
`LocalClassField.extensionWeilTransferReciprocity`. The final assembly (unit `GlobalAssembly`)
discharges them with these theorems.

## Result

`localPlaceRelation_of_global` (namespace `Langlands.LocalFactor.NonabelianBrauer`), universes:
fields in `Type`, representation carriers in `uV`.

Hypotheses:

- `hM : LocalRelativeWeilMapExistenceStatement`: local-to-relative Weil maps exist for geometric
  candidates;
- `hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement`: transfer reciprocity for
  extensions of p-adic fields;
- local invariant families `I` with `hI`, and a class family `c` with the four compatibilities
  `hc`;
- a Galois extension `E/k` of number fields;
- a finite family of intermediate fields `K j` with weights `r j` and Hecke characters `Λ₁ j`,
  `Λ₂ j`;
- the global relation `hrel`:
  `Σ_j r_j Ind_{W_{E/K_j}}([τ ∘ Λ₁ j] - [τ ∘ Λ₂ j]) = 0` in the continuous virtual group of
  `W_{E/k}`;
- a finite place `z₀` of `k` and a normalized reciprocity family `eC` of `k_{z₀}`.

Conclusion: `LocalPlaceRelation r K Λ₁ Λ₂ z₀ eC` (unit `PlaceEpsilon`). This is the local
relation `Σ_{(j,u)} r_j Ind([rec ∘ Λ₁ j_u] - [rec ∘ Λ₂ j_u]) = 0` over the places `u` of the
`K j` above `z₀`, with the transported candidates of `eC`.

Proof:

1. Choose a place `w` of `E` above `z₀` (`placeAbove`).
2. The candidate `ew` of `E_w` transported from `eC` is geometric, by the proved
   `LocalClassField.commonClosureGeometricProof`. So `hM` gives a local map `ι` with
   `IsLocalRelativeWeilMap`.
3. `localInducedRestriction_of_extensionSquare hsq` gives the local restriction formula for every
   `K j`.
4. Unit `LocalRelation` (`sum_induce_weilCharacter_eq_zero`) restricts the global relation along
   `ι`.
