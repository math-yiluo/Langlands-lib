# Relative dimension of the chosen dual over an algebraically closed field, conditionally

This module reduces the published proposition
`Langlands.AbelianScheme.AlgClosedFieldDualSchemeRelativeDimensionStatement.{u}` to three
Library statements that had no published proof when it was written. It does **not**
prove the target outright. Its main theorem is

```lean
theorem Langlands.AbelianScheme.algClosedFieldDualSchemeRelativeDimension_of_inputs
    (finitePresentation : RelativeDualSchemeFinitePresentationStatement.{u})
    (mumford : MumfordBundlePicardZeroStatement.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}) :
    AlgClosedFieldDualSchemeRelativeDimensionStatement.{u}
```

The three hypotheses are:

- `RelativeDualSchemeFinitePresentationStatement`: over a quasi-separated base, the chosen
  dual `dualScheme A hA` is locally of finite presentation;
- `MumfordBundlePicardZeroStatement`: the Mumford family of a rigidified line bundle is a
  Picard-zero family;
- `GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`: a smooth, proper,
  geometrically connected commutative group scheme over an algebraically closed field has
  an ample line bundle.

Each is imported as a statement only and passed as an explicit argument. Once proofs of
all three are published, applying this theorem to them proves the target exactly, with no
further hypothesis. Inspection of both theorems reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The file uses no `sorry`.

## Source and provenance

The target paraphrases Theorem (6.18) of Edixhoven, van der Geer and Moonen, *Abelian
Varieties* (printed p.96, PDF p.100; registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`): `Pic⁰_{X/k}` is an abelian variety
of dimension `dim X = dim_k H¹(X, O_X)`. Its proof combines three facts: an ample `L`
gives `φ_L : X → Pic⁰` with finite kernel, so `dim Pic⁰ ≥ dim X`; Corollary (6.6) (the
tangent space of `Pic` at the identity is `H¹(X, O_X)`, and `Pic⁰` is smooth exactly when
`dim Pic⁰ = dim H¹(X, O_X)`); and Proposition (6.15) (`dim H¹(X, O_X) ≤ dim X`). The Lean
proof uses the same three inequalities, but locally at the rational origin. It concludes
that the origin stalk is regular of dimension `g` and then spreads this over the dual by
translations. These group-scheme steps are derived content, not quoted from the source.

## `nonempty_grpObj_dualScheme`

For any base `S`, abelian scheme `A` and `hA : HasDualScheme A`, the over-scheme
`dualScheme A hA` has a group-object structure. The Poincaré family is tensor invertible
(`locallyFreeRankOneIffTensorInvertible`). Its inverse `N` gives a line bundle `M` and an
evaluation `P ⊗ M ≅ O` (`localizedTensorIso`). The published construction
`dualCommGroupSchemeFromEvaluation` then takes these data together with the published
coherence proofs `pullbackTensorComparisonIsIso`, `picardZeroPullback`,
`pullbackTensorComposition`, `pullbackTensorUnitCoherence`,
`explicitPullbackTensorAssociativity`, `tensorMonoidalLeftUnitorComparison` and
`pullbackTensorSymmetry`. Its underlying group object is the required `GrpObj`. This
mirrors the construction in the published `FieldDualSchemeSeparatedProof`.

## `algClosedFieldDualSchemeRelativeDimension_of`

This intermediate theorem proves the target from three hypotheses:
`RelativeDualSchemeFinitePresentationStatement`; for every field `k`, a `k`-linear
equivalence between the tangent space of the dual at `dualOrigin A hA` and
`H¹(A, O_A)`; and, for algebraically closed `K`, the bound
`g ≤ dim O_{A^∨, 0}` for the origin stalk. Write `D = dualScheme A hA`, `e = dualOrigin A hA`
and `x₀` for the image of the closed point under `e`. The proof:

1. `finitePresentation` makes `D` locally of finite presentation over `Spec K`.
   `nonempty_grpObj_dualScheme` gives a group law on `D`.
2. The published `fieldPointTangentLocalRegularity` gives
   `dim T = dim of the cotangent space of O_{D, x₀}`, where `T` is the tangent space. It
   also says that `dim T ≤ g ≤ dim O_{D, x₀}` implies that `O_{D, x₀}` is regular.
   `dim T ≤ g` follows from the tangent equivalence and the published
   `fieldStructureSheafH1DimensionBound` (`dim H¹(A, O_A) ≤ g`). The lower bound supplies
   `g ≤ dim O_{D, x₀}`. So `O_{D, x₀}` is a regular local ring. Since for a regular local
   ring the Krull dimension equals the cotangent dimension
   (`IsRegularLocalRing.iff_finrank_cotangentSpace`), `dim O_{D, x₀} = g`.
3. A regular local ring is a domain (`IsRegularLocalRing.isDomain`, from the published
   `AnthropicFLT` port `Thm_IsRegularLocalRing_isDomain`).
4. `x₀` is a closed point (`pointEquivClosedPoint`). For every closed point `y`,
   `GrpObj.exists_iso_apply_closedPoint` (module `FieldGroupSchemeHomogeneity`) gives an
   automorphism of `D` over `K` sending `x₀` to `y`. Its stalk map is a ring isomorphism
   `O_{D, y} ≅ O_{D, x₀}`. Hence every closed-point stalk is reduced and has Krull
   dimension `g`.
5. `D` is Jacobson (locally of finite type over a field), so
   `isReduced_of_isReduced_stalk_closedPoint` makes `D` reduced.
6. The published `closedPointHomogeneousSmooth` (a reduced scheme, locally of finite type
   over an algebraically closed field, whose automorphisms act transitively on closed
   points, is smooth), with the same homogeneity lemma, makes `D.hom` smooth.
7. `smoothOfRelativeDimension_of_ringKrullDim_stalk` (module `FieldGroupSchemeHomogeneity`)
   and step 4 give `SmoothOfRelativeDimension g D.hom`.

## `algClosedFieldDualSchemeRelativeDimension_of_inputs`

This theorem supplies the two non-Library hypotheses of the previous theorem from proved
modules:

- the tangent equivalence is `dualSchemeTangentH1 A hA`, proved by Worker 299 in module
  `Langlands.AlgebraicGeometry.Picard.DualSchemeTangentH1`;
- the lower bound is `algClosedFieldDualOriginDimensionLowerBound_of mumford
  finitePresentation ample`, from module
  `Langlands.AlgebraicGeometry.Picard.DualOriginMumfordClassifier`. That module is itself
  conditional on the three displayed statements.

## Imports

- the target statement module and the statement modules
  `RelativeDualSchemeFinitePresentationStatement`, `MumfordBundlePicardZeroStatement` and
  `AlgebraicallyClosedFieldAmpleExistenceStatement` (the latter two through
  `DualOriginMumfordClassifier`);
- `DualGroupScheme` and the published coherence proofs `LocalComparisonProof`,
  `PicardZeroPullbackProof`, `Modules.PullbackTensorProof`,
  `Modules.PullbackTensorCompatibilityProofs`, `Modules.PullbackTensorUnitProofs`,
  `Modules.ExplicitPullbackTensorAssociativityProofs` and
  `Modules.TensorMonoidalComparisonProofs`;
- the published proofs `FieldPointTangentLocalRegularityProof`,
  `FieldStructureSheafH1DimensionBoundProof`, `ClosedPointHomogeneousSmoothProof` and
  `AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain`;
- the helper modules `FieldGroupSchemeHomogeneity`, `Picard.DualSchemeTangentH1` and
  `Picard.DualOriginMumfordClassifier`.

None of these modules imports `AlgClosedFieldAmpleMumfordEulerSquareStatement` or
`AlgClosedFieldMumfordDualEulerStatement`.
