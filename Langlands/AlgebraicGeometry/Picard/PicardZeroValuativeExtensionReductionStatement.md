# Valuative extension of Picard-zero classes from four focused propositions

`Langlands.AbelianScheme.PicardZeroValuativeExtensionReductionStatement.{u}` is the proposition

```lean
AlgClosedFieldTranslationDifferenceLiftingStatement.{u} →
  Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u} →
    MumfordBundlePicardZeroStatement.{u} →
      ValuationRingAmpleExtensionStatement.{u} →
        PicardZeroValuativeExtensionStatement.{u}
```

in module `Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionReductionStatement`,
inside `namespace Langlands.AbelianScheme`. This unit only defines the proposition. It proves
nothing, in particular none of the five named propositions. It says only that the last one
follows from the first four.

## The five propositions

All five are existing Prop-valued definitions of the Library, used unchanged at the same
universe `u`. Here `preservation` always denotes a proof of the Library proposition
`pullbackTensorComparisonIsIsoStatement`.

- `Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement` (module
  `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingStatement`),
  the first hypothesis. Let `A` be an abelian scheme over `Spec K` with `K` algebraically
  closed. Let `L`, `N` be line bundles on `A.X.left` with an isomorphism
  `L ⊗ N ≅ 𝒪`, and let `P` be a line bundle. If `L` is ample and `P` is translation invariant
  (`GroupScheme.IsTranslationInvariant A.toGrp P`), then some `K`-point `x` of `A` satisfies
  `t_x^*L ⊗ N ≅ P`.
- `Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement` (module
  `Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`), the second
  hypothesis. Every commutative group object `G` of schemes over `Spec K`, with `K`
  algebraically closed, whose structure morphism is smooth, proper and geometrically connected,
  has an ample line bundle on `G.X.left`.
- `Langlands.AbelianScheme.MumfordBundlePicardZeroStatement` (module
  `Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroStatement`), the third hypothesis.
  For every abelian scheme `A` over any scheme `S`, every line bundle `L` on `A.X.left`
  rigidified along `unitSection A`, and every line bundle `M` with an isomorphism
  `L ⊗ M ≅ 𝒪`, the Library's rigidified Mumford family
  `mumfordBundle A preservation L M evaluation` satisfies `IsPicardZeroFamily`.
- `Langlands.AbelianScheme.ValuationRingAmpleExtensionStatement` (module
  `Langlands.AlgebraicGeometry.Picard.ValuationRingAmpleExtensionStatement`), the fourth
  hypothesis. Let `R` be a valuation domain with fraction field `K` and `A` an abelian scheme
  over `Spec R`. If the generic fibre `A ×_{Spec R} Spec K` has an ample line bundle, then some
  line bundle on `A.X.left` has ample pullback to the generic fibre along the first projection.
- `Langlands.AbelianScheme.PicardZeroValuativeExtensionStatement` (module
  `Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionStatement`), the conclusion.
  Let `S` be a quasi-separated scheme, `A` an abelian scheme over `S`, `R` a valuation domain
  with fraction field `K`, `i₂ : Spec R ⟶ S`, and `q` a class in
  `PicardZeroClasses A (Over.mk (Spec K ⟶ Spec R ⟶ S))`. Then there are a valuation domain
  `R'` with fraction field `K'`, a local ring map `φ : R →+* R'` and a ring map `ψ : K →+* K'`
  with `algebraMap R' K' ∘ φ = ψ ∘ algebraMap R K`, and a class `q'` in
  `PicardZeroClasses A (Over.mk (Spec.map φ ≫ i₂))`. The pullback of `q'` along
  `Spec K' ⟶ Spec R'` equals the pullback of `q` along `Spec.map ψ`, both computed with
  `RigidifiedLineBundle.classesPullback` over `Spec K'`.

## Provenance

Internal. The implication is the decomposition step of proof task
`322a2874-8b1c-4e61-b7cc-e0d154742640`, whose target is the conclusion. It adds no mathematics
of its own; the geometric input is in the four hypotheses, whose Markdown cites the
literature. The assembly runs as follows.

1. Replace `K` by an algebraic closure `K'` and `R` by a valuation ring `R'` of `K'` dominating
   `R`.
2. Over `K'` the translation-invariant class is `t_x^*L ⊗ N` with `L` ample. This is Mumford,
   *Abelian varieties*, §8 Theorem 1, which is the first hypothesis.
3. The ample bundle exists by the second hypothesis. It may be taken to be the generic
   restriction of a line bundle over `R'`, by the fourth hypothesis (Raynaud, LNM 119,
   Théorème XI 1.4).
4. The point `x` extends over `R'` by the valuative criterion for the proper structure
   morphism of the abelian scheme.
5. The class over `R'` is the pullback of the rigidified Mumford family along the extended
   point. It is Picard zero by the third hypothesis.

A Lean proof of the implication is a separate unit.
