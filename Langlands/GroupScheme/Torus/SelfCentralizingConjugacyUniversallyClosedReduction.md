# Reducing universal closedness of the conjugacy map to valuative lifting

This module defines
`Langlands.GroupScheme.SelfCentralizingConjugacyUniversallyClosedReduction.algClosedPointLift`,
a chosen lift of a point with values in an algebraically closed field. It also
proves
`Langlands.GroupScheme.SelfCentralizingConjugacyUniversallyClosedReduction.selfCentralizingConjugacyUniversallyClosed_of_valuationLift`:

> `TorusSubgroupModuli.GeneralLinearAffineSumStatement.{u}` and
> `SelfCentralizingConjugacyValuationLiftStatement.{u}` together imply
> `SelfCentralizingConjugacyUniversallyClosedStatement.{u}`.

The universal-closedness statement asserts that every factorization `φ : Y ⟶ M`
of the conjugacy map `f : G.X ⟶ M` through the normalizer quotient
`p : G.X ⟶ Y` is universally closed. The proof uses Mathlib's
`universallyClosed_eq_universallySpecializing`: a morphism is universally closed
exactly when it is quasi-compact and every base change of it lifts
specializations. Quasi-compactness comes from the first premise, the
specialization lifting from the second. The module adds no geometric input.

## Auxiliary results

- `exists_algClosedPoint_lift`: let `q : X ⟶ Y` be surjective and locally of
  finite type, and let `Ω` be an algebraically closed field. Every morphism
  `a : Spec Ω ⟶ Y` equals `x ≫ q` for some `x : Spec Ω ⟶ X`. The fibre product
  `X ×_Y Spec Ω` is locally of finite type over `Spec Ω` and nonempty, because
  its projection to `Spec Ω` is surjective. The Library's
  `ClosedRationalPoints.exists_rationalPoint_mem` gives it an `Ω`-rational
  point. Its composite with the first projection is `x`.
- `algClosedPointLift q a` (the definition) is the point `x` chosen by
  `exists_algClosedPoint_lift`. `algClosedPointLift_comp` records
  `algClosedPointLift q a ≫ q = a`.
- `hasAlgClosedValuationLifts_of_isPullback`: the Library's property
  `Langlands.AlgebraicGeometry.HasAlgClosedValuationLifts` is stable under base
  change. Given a pullback square with `f' : X' ⟶ Y'` the base change of
  `f : X ⟶ Y` and a test square for `f'`, compose it with the square, lift for
  `f`, and combine the lift with the given point of `Y'` through the universal
  property of the pullback.
- `quasiCompact_of_disjointAffineCover`: a morphism `φ : Y ⟶ M` from a
  quasi-compact scheme is quasi-compact when `M` is the union of pairwise
  disjoint affine opens `U k`. Each `U k` is closed, since its complement is the
  union of the others. So `φ⁻¹(U k)` is a closed, hence quasi-compact, subset of
  `Y`. Quasi-compactness is local on the target
  (`IsZariskiLocalAtTarget.of_iSup_eq_top`), and over an affine target it means
  that the source is quasi-compact (`HasAffineProperty.iff_of_isAffine`).

## The main theorem

`selfCentralizingConjugacyUniversallyClosed_of_valuationLift hGL hV` takes the
hypotheses of `SelfCentralizingConjugacyUniversallyClosedStatement` and a map
`φ : Y ⟶ M` with `p ≫ φ = f`.

1. `φ.left` is a monomorphism. The maps `p` and `f` have the same fibres on every
   test object, by the hypothesis on `p` and
   `SelfCentralizingConjugacyClosedEmbeddingReduction.comp_eq_iff_mem_torusNormalizer`.
   Since `p` is an epimorphism
   (`SelfCentralizingConjugacyClosedEmbeddingReduction.epi_of_fppf`), `φ` equals
   the descended map `HomogeneousQuotientComparison.desc p f`, whose underlying
   morphism is a monomorphism by
   `SelfCentralizingConjugacyClosedEmbeddingReduction.mono_desc_of_fppf_fiber_iff`.
2. `φ.left` is quasi-compact. `G.X.left` is quasi-compact, since `G.X.hom` is
   quasi-compact over the affine `Spec R`. So `Y.left` is quasi-compact, being
   the image of the surjective `p.left`. The premise
   `GeneralLinearAffineSumStatement` writes `M.left` as a union of pairwise
   disjoint affine opens, and `quasiCompact_of_disjointAffineCover` applies.
3. `φ.left` has lifts for valuation subrings of algebraically closed fields
   (`HasAlgClosedValuationLifts`). Let `A` be a valuation subring of an
   algebraically closed field `Ω`, with `b : Spec A ⟶ M.left` and
   `a : Spec Ω ⟶ Y.left` such that `a ≫ φ.left = ι ≫ b`, where `ι` is
   `Spec Ω ⟶ Spec A`. Put `g = algClosedPointLift p.left a`, a point of `G` with
   `g ≫ p.left = a`. Then `ι ≫ b = g ≫ f.left`, and the premise
   `SelfCentralizingConjugacyValuationLiftStatement` gives
   `h : Spec A ⟶ G.X.left` with `h ≫ f.left = b`. The lift is `h ≫ p.left`. It
   maps to `b` because `p.left ≫ φ.left = f.left`. Its restriction to `Spec Ω`
   is `a`, because both have the same composite with the monomorphism
   `φ.left`.
4. By `hasAlgClosedValuationLifts_of_isPullback`, every base change of `φ.left`
   has the same lifts, so it lifts specializations by the Library's
   `Langlands.AlgebraicGeometry.specializingMap_of_algClosed_valuation_lifts`.
   With step 2 and `universallyClosed_eq_universallySpecializing`, `φ.left` is
   universally closed.

## Provenance

This is an internal assembly step of Task 7782 and follows no particular source.
It reduces universal closedness to the valuative form recorded in
`SelfCentralizingConjugacyValuationLiftStatement`. The characterization of
universally closed morphisms as quasi-compact morphisms whose base changes lift
specializations is taken from Mathlib (`universallyClosed_eq_universallySpecializing`),
and the passage from valuative lifts to lifting specializations from the Library
(`specializingMap_of_algClosed_valuation_lifts`). Together they amount to the
existence part of the valuative criterion for universal closedness, tested on
valuation rings of algebraically closed fields.
