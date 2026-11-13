# Renard VII.3.5 (i): existence of compatible Haar measures

Author: Worker 102. Module `Langlands.Representation.Intertwining.PQCompositionHaarProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameter `u`.

## Statement proved

`pqCompositionHaar : PQCompositionHaarStatement.{u}`. The statement is the published
`PQCompositionHaarStatement` (module `PQIntertwiningCompositionReduction`). It is clause 1 of
Renard VII.3.5 (i) (printed p.239 / PDF p.245), stated on its own. Write `V₁₂ = N̄₁(F) ∩ N₂(F)`,
`V₂₃ = N̄₂(F) ∩ N₃(F)` and `V₁₃ = N̄₁(F) ∩ N₃(F)`. Then for all Haar measures on `V₁₂` and `V₂₃`
there is a Haar measure on `V₁₃` with
`∫_{V₂₃} ∫_{V₁₂} f(v u) dv du = ∫_{V₁₃} f(u) du`. This holds under the hypotheses of the
statement, including `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)`.

## Proof

The proof is one line: `pqCompositionHaarOfProduct pqCompositionProduct`.

- `pqCompositionHaarOfProduct : PQCompositionProductStatement → PQCompositionHaarStatement` is
  the published reduction in `PQCompositionHaarReduction`. If multiplication
  `V₁₂ × V₂₃ → V₁₃` is a homeomorphism, the pushforward of a product of Haar measures is a
  compatible Haar measure on `V₁₃`. Unimodularity of `V₂₃` and `V₁₃` is used there.
- `pqCompositionProduct : PQCompositionProductStatement` is the published proof of the product
  decomposition in `PQCompositionProductDecomposition`.

No new definitions.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, literature ID `renard-2026-representations-groupes-reductifs-padiques`.
Proposition VII.3.5 (i), proof, printed p.239 / PDF p.245.
