# Renard VII.3.5 (i): proof of the composition of the operators `J_{Q|P}`

Authors: Worker 48 and Worker 102. Worker 102 proved inputs (2)–(4) and drafted the same term
independently. Module `Langlands.Representation.Intertwining.PQIntertwiningCompositionProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.

This module proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.PQIntertwiningCompositionStatement`
(module `Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements`, unchanged) by
the theorem

```
theorem pqIntertwiningComposition : PQIntertwiningCompositionStatement.{u, v}
```

with no added hypothesis. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, VII.3.5 (i), printed pp.236–240 / PDF pp.242–246. Literature ID
`renard-2026-representations-groupes-reductifs-padiques`.

For parabolics `P₁, P₂, P₃` with common Levi `M` and `d(P₁, P₃) = d(P₁, P₂) + d(P₂, P₃)`,
`d(P₁, P₂) = 1`, the statement says that Haar measures on `N̄₁ ∩ N₂`, `N̄₂ ∩ N₃` and
`N̄₁ ∩ N₃` compatible with the product decomposition exist. With such measures, every
`P₁P₃`-regular `σ` is `P₁P₂`- and `P₂P₃`-regular, and the integral-normalized operators of
VII.3.4 satisfy `J_{P₃|P₁}(σ) = J_{P₃|P₂}(σ) ∘ J_{P₂|P₁}(σ)`.

## Proof

The proof is one term. It applies the Library reduction
`pqIntertwiningComposition_of_reductions` (module `PQIntertwiningCompositionReduction`) to proofs
of its four inputs, all of them in the Library:

```
theorem pqIntertwiningComposition : PQIntertwiningCompositionStatement.{u, v} :=
  pqIntertwiningComposition_of_reductions pqBoundaryVanishingCompactSupport pqCompositionProduct
    pqCompositionHaar pqCompositionRegularity
```

- `pqBoundaryVanishingCompactSupport` (module `PQBoundaryVanishingCompactSupportProof`): proves
  `PQBoundaryVanishingCompactSupportStatement`. A function lies in `F̃^{<1̄}_{PQ}` if and only if
  its restriction to `N̄ ∩ U` has compact support.
- `pqCompositionProduct` (module `PQCompositionProductDecomposition`): proves
  `PQCompositionProductStatement`. Multiplication `(N̄₁ ∩ N₂) × (N̄₂ ∩ N₃) → N̄₁ ∩ N₃` is a
  homeomorphism on rational points.
- `pqCompositionHaar` (module `PQCompositionHaarProof`): proves
  `PQCompositionHaarStatement`, the existence of compatible Haar measures, by applying
  `pqCompositionHaar_of_product` to `pqCompositionProduct`.
- `pqCompositionRegularity` (module `PQCompositionLeviIntersection`): proves
  `PQCompositionRegularityStatement`. `P₁P₃`-regularity implies `P₂P₃`- and `P₁P₂`-regularity.

The reduction proves the operator identity by uniqueness (`pqIntertwiner_eq_of_eval_one`): for
`P₁P₃`-regular `σ`, two intertwining operators `i_{P₁}^G(σ) → i_{P₃}^G(σ)` that agree at `1` on
every `f ∈ F̃^{<1̄}_{P₁P₃}(σ)` are equal. `J_{P₃|P₂} ∘ J_{P₂|P₁}` and `J_{P₃|P₁}` agree there
(`eval_one_comp_eq_of_integral_formulas`), because the integral formulas of VII.3.4 combine
through the product decomposition and the compatible measures.
