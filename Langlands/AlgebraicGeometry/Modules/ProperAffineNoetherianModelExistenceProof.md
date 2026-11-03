# Proof of noetherian approximation for a proper scheme with two modules

Module `Langlands.AlgebraicGeometry.Modules.ProperAffineNoetherianModelExistenceProof`, universe
`u`. Authors: Worker 1038 and Worker 59. It proves the published proposition
`Langlands.AlgebraicGeometry.Modules.ProperAffineNoetherianModelExistenceStatement` of
[`ProperAffineNoetherianModelExistenceStatement`](ProperAffineNoetherianModelExistenceStatement.md),
which it imports unchanged:

```lean
theorem properAffineNoetherianModelExistence :
    ProperAffineNoetherianModelExistenceStatement.{u}
```

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Inputs

The proof is an assembly of published descent results, each of the form "a property over `A`
descends to some finitely generated `A₀`-subalgebra `T ⊆ A` containing a prescribed finite set":

- `NoetherianApproximation.schemeSubalgebraDescent` (the scheme and the morphism),
- `NoetherianApproximation.isSeparatedSubalgebraDescent` and
  `NoetherianApproximation.isProperSubalgebraDescent` (separatedness, properness),
- `NoetherianApproximation.finitePresentationModuleSubalgebraDescent` (finitely presented
  module sheaves, by Worker 1038, Stacks 01ZR),
- `NoetherianApproximation.isFlatOverSubalgebraDescent` (flatness of a finitely presented module
  over the base, by Worker 59, Stacks 05LY),

together with the pasting lemmas `NoetherianReduction.exists_isPullback_subalgebra`,
`NoetherianReduction.exists_isPullback_subalgebra'`,
`NoetherianReduction.iff_pullback_snd_of_isPullback` and
`NoetherianReduction.isNoetherianRing_of_fg` of
`Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsNoetherianReduction`.

## Proof

Fix a commutative ring `A`, a proper locally finitely presented `p : Y ⟶ Spec A`, finitely
presented `M, N : Y.Modules` and `IsFlatOver p N`. The proof passes through six stages; at each
stage `T` is a noetherian ring with `Algebra T A`, and there is a pullback square
`IsPullback aᵢ p fᵢ (Spec.map (algebraMap T A))`. Every new stage ring `T'` is a finitely
generated `T`-subalgebra of `A` (`T' : Subalgebra T A` with `T'.FG`), so it contains the image of
the previous stage `T`; it is of finite type over the noetherian ring `T`, hence noetherian by
`NoetherianReduction.isNoetherianRing_of_fg`. The new square is obtained by pasting with the
base change along `T → T'` (`exists_isPullback_subalgebra` or `exists_isPullback_subalgebra'`).

1. **`exists_model`.** The prime subring `⊥ : Subalgebra ℤ A` is a finitely generated
   `ℤ`-algebra, hence noetherian. `schemeSubalgebraDescent` with `A₀ := ⊥` gives a finitely
   generated `T₁` and `f₁ : X₁ ⟶ Spec T₁` locally of finite presentation, quasi-compact and
   quasi-separated, with `p` its base change.
2. **`exists_model_of_finitePresentation`.** `p` is separated, so the chosen base change
   `pullback.snd f₁ _` is separated (`iff_pullback_snd_of_isPullback`), and
   `isSeparatedSubalgebraDescent` gives `T₂`. The intermediate base change `f₂` is separated,
   while quasi-compactness and local finite presentation pass to it by base change
   (`MorphismProperty.of_isPullback`).
3. **`exists_model_of_isSeparated`.** In the same way `isProperSubalgebraDescent` gives `T₃`
   with `f₃` proper and locally of finite presentation.
4. **`exists_model_of_isProper`.** `finitePresentationModuleSubalgebraDescent`, applied to `f₃`
   (proper, so quasi-compact, separated and locally of finite type) and `M`, gives `T₄` and a
   finitely presented `M₄` on the `T₄`-stage whose pullback along every map satisfying the stage
   equations is isomorphic to `M`; it is applied to the map `a₄` of the pasted square.
5. **`exists_model_of_module`.** The same theorem applied to `N` gives `T₅` and `N₅`. The pullback
   of `M₄` to the `T₅`-stage is finitely presented (`isFinitePresentation_pullback`) and its
   pullback along `a₅` is `M`, by `Scheme.Modules.pullbackComp` and `pullbackCongr`.
6. **`exists_model_of_modules`.** `IsFlatOver p N` transfers to the pullback of `N₅` along `a₅`
   through the isomorphism `eN` (`isFlatOver_iff_of_iso`), and `isFlatOverSubalgebraDescent`
   gives `T₆` such that, for every pullback square of `f₅` along `Spec T₆ ⟶ Spec T₅`, the pullback
   of `N₅` along its upper map is flat over `Spec T₆`. The model is the `T₆`-stage
   `pullback.snd f₅ (Spec.map (algebraMap T₅ T₆))`, which is proper and locally of finite
   presentation by base change, with the pullbacks of `M₅` and `N₅` along the first projection
   as module sheaves. These are finitely presented, the second is flat over `Spec T₆`, and the
   pasted square from `exists_isPullback_subalgebra` together with the composites of
   `pullbackComp`, `pullbackCongr` and the earlier isomorphisms supplies the Cartesian square and
   the isomorphisms required by `HasAffineNoetherianModel p M N`, with `R₀ := T₆`.

The main theorem introduces the data of the proposition and applies `exists_model`.

## Provenance

This follows the route described in
[`ProperAffineNoetherianModelExistenceStatement`](ProperAffineNoetherianModelExistenceStatement.md):
Stacks Project, *Limits of Schemes* (`limits.tex`, commit `a04446e5`), Lemmas 01ZM, 01ZR, 05LY
and 081F, applied to the filtered system of finitely generated `ℤ`-subalgebras of `R`. The
staged structure of the proof (one descent per stage, with pasted pullback squares) mirrors the
Library's `NoetherianReduction` module. The stage lemmas in this module are internal.
