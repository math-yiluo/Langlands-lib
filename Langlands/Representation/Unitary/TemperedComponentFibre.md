# The smoothed maps of a cone element for the global relations

Module `Langlands.Representation.Unitary.TemperedComponentFibre` takes a bounded cone element `F`
for the relations `globalRel` of
`Langlands.Representation.Unitary.TemperedComponentGlobalKernel` and constructs, on the Hilbert
space `VL hF` of `Langlands.Representation.Unitary.TemperedComponentGNS`, the bounded maps

`opB hF hB k = (w ↦ vec 1 k w)^* ∘ iotaL hF : VL hF → W`,

so that `⟪w, B_k (vecL' y k' w')⟫ = F (k, k', y, w, w')` (`inner_opB_vec`).

## Results

| Declaration | Content |
| --- | --- |
| `wordOp_sigma_vec` | `σ(a) (vecL' y k w) = vecL' (π(a) y) k w` for words `a`, by induction from `sigma_vec` and `testOp_sigma_vec` |
| `opB_relation` | `B_{nIdx n} σ(a) σ(ψ_k) = π_W(ψ_{nIdx n}) π_W(a) B_k`: on spanning vectors both sides pair with `w` to the two sides of the word relation of `globalRel` |
| `opB_mem_wSub` | `B_k` takes values in `W₀`: the support relation gives `⟪w, B_k v⟫ = ⟪P_{W₀} w, B_k v⟫`, so `B_k v = P_{W₀} (B_k v)` |
| `exists_opB_ne_zero` | if `F ≠ 0` and `ψ_{nIdx n}` is an approximate identity, some `B_k` is nonzero |

For the last item: if every `B_k` vanished, `F (k, k', y, ·, ·)` would vanish for `y` in the left
ideal. The word relation with the empty word and `x = 1` then gives
`⟪(π_W(χ_n))^* u, z⟫ = 0` for all `u`, where `F (k, k', 1, u, w') = ⟪u, z⟫`; so `π_W(χ_n) z = 0` for all
`n`, hence `z = 0` by the approximate identity. Thus `F (k, k, 1, w, w) = ‖vec 1 k w‖² = 0`, so
`vec 1 k w = 0` and `F = 0`.

## Provenance

Internal; these maps are the analogues, at an extreme point, of the fibre maps `B_{ψ,z}` of the
proof sketch in the Markdown of `Langlands.Analysis.TemperedIrreducibleComponentStatement`.
