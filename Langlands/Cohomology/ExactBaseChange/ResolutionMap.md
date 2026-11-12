# The cochain map of a base-change square on resolutions

Helper module for the proof of
`Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement`
(see [the proof](../../AlgebraicGeometry/Modules/FlatHigherDirectImageBaseChangeProof.md)). Namespace
`Langlands.Cohomology.ExactBaseChange`. It contains no scheme theory.

## Setting

`F₁ : C₁ ⥤ D₁`, `F₂ : C₂ ⥤ D₂`, `α : C₁ ⥤ C₂` and `β : D₁ ⥤ D₂` are additive
functors between abelian categories, and `τ : F₁ ⋙ β ⟶ α ⋙ F₂` is a natural
transformation. `baseChangeNatTrans τ n : F₁.rightDerived n ⋙ β ⟶ α ⋙ F₂.rightDerived n`
is the published base change transformation (module
`Langlands.Cohomology.ExactBaseChange`).

## Declarations

- `isIso_resolutionComparison_of_acyclic F ε hK n`: for a left exact additive
  `F` and a right resolution `ε : A[0] ⟶ K` whose terms satisfy
  `R^{r+1} F (K.X i) = 0`, the published comparison
  `AcyclicResolution.resolutionComparison F ε n : Hⁿ(F K) ⟶ Rⁿ F A` is an
  isomorphism. Proof: the second component of the published
  `acyclicResolutionComparisonStatement`, applied to Mathlib's chosen injective
  resolution of `A` and the lift of `comp_lift_id`; `resolutionComparison` is
  by definition that comparison.
- `resolutionBaseChangeMap τ ψ`: for cochain complexes `K` over `C₁`, `K'`
  over `C₂` and a cochain map `ψ : α K ⟶ K'`, the cochain map
  `β (F₁ K) ⟶ F₂ K'` with components `τ.app (K.X q) ≫ F₂.map (ψ.f q)`. It is the
  map `Φ` of the published `ResolutionCompatibilityStatement`. The chain map
  condition follows from the naturality of `τ` at the differentials of `K` and
  the chain map condition of `ψ`. `resolutionBaseChangeMap_f` records the
  components (`rfl`).
- `isIso_map_baseChangeNatTrans_app_iff τ ε ε' ψ hψ hK hK' γ n`: let `ε` and
  `ε'` be right resolutions of `A` and of `α A` whose terms are acyclic for `F₁`
  and `F₂`, and let `ψ` satisfy `mapResolutionAugmentation α ε ≫ ψ = ε'`. With
  `C₁`, `C₂` having injective resolutions, `α`, `β`, `F₁`, `F₂` left exact and
  `α`, `β` preserving homology, for every functor `γ : D₂ ⥤ E` and every `n`,
  `γ.map ((baseChangeNatTrans τ n).app A)` is an isomorphism if and only if
  `γ.map (Hⁿ (resolutionBaseChangeMap τ ψ))` is.

## Proof of the criterion

The first conjunct of the published theorem
`resolutionCompatibility : ResolutionCompatibilityStatement` (module
`Langlands.Cohomology.ExactBaseChange.ResolutionProof`) gives

`β.map (resolutionComparison F₁ ε n) ≫ (baseChangeNatTrans τ n).app A =
  inv (homologyNatTrans β _ n).app (F₁ K) ≫ Hⁿ(resolutionBaseChangeMap τ ψ) ≫
  resolutionComparison F₂ ε' n`.

The two resolution comparisons are isomorphisms by
`isIso_resolutionComparison_of_acyclic`, and `homologyNatTrans β` is an
isomorphism since `β` preserves homology. Solving for the component
(`IsIso.eq_inv_comp`), applying `γ` and cancelling the outer isomorphisms with
Mathlib's `isIso_comp_left_iff` and `isIso_comp_right_iff` gives the
equivalence.

Provenance: internal homological algebra; the formula is the published
resolution compatibility statement, motivated by The Stacks Project, Lemma
02N7. The proof uses only the standard axioms.
