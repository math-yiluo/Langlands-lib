# Selected weight parts of a split representation

Author: Worker 1221. Module `Langlands.Representation.Exponents.SelectedWeightSplitting`.
This is an internal supporting module for the proof of Renard VII.2.5
(`TemperedGeometricLemmaStatement`). It contains generic linear algebra about the selected
weight parts `selectedWeightPart` of Worker 1725's module
`Langlands.Representation.Exponents.SelectedWeights`, together with two facts about
normalized induction. Nothing here is specific to reductive groups.

Recall from `SelectedWeights` that for a representation `π` of a topological group `M`,
a homomorphism `ι : A →* M` into the center and a predicate `P` on characters
`A →* Rˣ`, `selectedWeightPart π ι hι P` is the subrepresentation
`⨆ χ, ⨆ (_ : P χ), generalizedWeightSpace π ι χ hι`, the sum of the generalized weight
spaces of `A` (acting through `ι`) over the selected characters.

## Declarations

In namespace `Langlands`:

| Lean name | Content |
| --- | --- |
| `selectedWeightPart_eq_top_of_forall` | If the generalized weight spaces of `π` span (`⨆ χ, generalizedWeightSpace π ι χ hι = ⊤`) and every `χ` with a nonzero generalized weight space satisfies `P`, then `selectedWeightPart π ι hι P = ⊤`. |
| `selectedWeightPart_toSubmodule_eq_range` | Let `π` be smooth, `i₀ : π₀ → π` and `i₁ : π₁ → π` intertwiners, and `p₀ : V → V₀`, `p₁ : V → V₁` arbitrary maps with `i₀ (p₀ v) + i₁ (p₁ v) = v` for all `v`. If the selected part of `π₀` for `P` is everything and the selected part of `π₁` for `¬ P` is everything, then the selected part of `π` for `P` is the range of `i₀`. |
| `nonempty_selectedWeightPart_equiv` | Under the same hypotheses and with `i₀` injective, there is an equivalence of representations (`Representation.Equiv`) from the selected part of `π` to `π₀`. |
| `subrepresentationProjection S T h` | For complementary subrepresentations `S`, `T` of `ρ` (`h : IsCompl S.toSubmodule T.toSubmodule`), the projection onto `S` along `T` as an intertwiner `ρ → S.toRepresentation`. It is `Submodule.projectionOnto` (`subrepresentationProjection_apply`). |
| `subrepresentationProjection_add` | The two complementary projections, viewed in `V`, add up to the identity. |
| `subrepresentationInclusion S ι` | The inclusion of a subrepresentation as an intertwiner, after restricting both actions along a monoid map `ι : H →* G` (`subrepresentationInclusion_apply`: it is the coercion). |
| `SmoothRep.subrepresentationProjection A S T h` | The same projection as a morphism of smooth representations `A ⟶ SmoothRep.subrepresentation A S`. |
| `SmoothRep.subtype_subrepresentationProjection_add` | The two projections followed by the morphisms `SmoothRep.subtype` add up to the identity of `A`. |
| `Aubert.General.normalizedInductionFunctor_map_add_map` | For a semidirect decomposition `P = M ⋉ U` of a locally compact nonarchimedean group `G` with `U` closed, normalized induction `normalizedInductionFunctor h hU` carries a splitting `i₀ ∘ p₀ + i₁ ∘ p₁ = id` of smooth complex representations of `M` to the same identity for the induced morphisms. |
| `Aubert.General.normalizedInductionFunctor_map_injective` | Normalized induction preserves injectivity of morphisms. |

## Proofs

- `selectedWeightPart_eq_top_of_forall`: compare the two suprema of submodules
  (`selectedWeightPart_toSubmodule`). A character with a zero weight space contributes
  `⊥`; every other one is selected.
- `selectedWeightPart_toSubmodule_eq_range`: images of selected vectors under an
  intertwiner are selected (`map_mem_selectedWeightPart`). For a selected `v`, the vector
  `i₁ (p₁ v) = v - i₀ (p₀ v)` is selected for `P` and also for `¬ P`. These two parts are
  disjoint for smooth `π` (`selectedWeightPart_disjoint`), so `i₁ (p₁ v) = 0` and
  `v = i₀ (p₀ v)`. Conversely the range of `i₀` is selected.
- `nonempty_selectedWeightPart_equiv`: corestrict `i₀` to the selected part. The result is
  bijective, by injectivity of `i₀` and the previous lemma, so `IntertwiningMap.ofBijective`
  gives the equivalence; the statement uses its inverse.
- The projection is an intertwiner because both summands are invariant: decompose `v` and
  use `Submodule.projectionOnto_apply_of_mem_left/right`.
- `normalizedInductionFunctor_map_add_map`: induced morphisms act pointwise on functions
  `G → X`, so the identity holds at each point by the hypothesis.
- `normalizedInductionFunctor_map_injective` is the published `normalizedInductionMap_injective`
  of `Aubert/General/InductionEmbeddings.lean`.

## Provenance

These are elementary facts, derived for the proof of Renard VII.2.5 (David Renard,
*Représentations des groupes réductifs p-adiques*, 2026, VII.2.5, printed p.230 / PDF
p.236). The proof there splits each `r^M_{w·Q∩M} W` into its unitary part and its
nonunitary part and compares exponents of the two resulting pieces. The source does not
state these lemmas separately. `nonempty_selectedWeightPart_equiv` is how the proof module
`TemperedGeometricPiece` identifies the unitary part of a geometric-lemma piece.
