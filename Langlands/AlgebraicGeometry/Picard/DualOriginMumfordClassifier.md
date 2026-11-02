# The Mumford classifier into the chosen dual and the origin dimension bound, conditionally

This module builds, for an abelian variety `A` over a field `k` with chosen dual
`dualScheme A hA`, the morphism `A → A^∨` that classifies the Mumford family of a line
bundle `L`. Over an algebraically closed field it then proves the local-dimension bound

```lean
theorem Langlands.AbelianScheme.algClosedFieldDualOriginDimensionLowerBound_of
    (mumford : MumfordBundlePicardZeroStatement.{u})
    (finitePresentation : RelativeDualSchemeFinitePresentationStatement.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ)
    (hg : A.HasRelativeDimension g) :
    (g : WithBot ℕ∞) ≤ ringKrullDim ((dualScheme A hA).left.presheaf.stalk
      ((dualOrigin A hA).left (IsLocalRing.closedPoint K)))
```

The theorem is **conditional**. Its three hypotheses are published Library statements that
had no published proof when this module was written:

- `Langlands.AbelianScheme.MumfordBundlePicardZeroStatement`: the Mumford family
  `mumfordBundle A preservation L M evaluation` is a Picard-zero family;
- `Langlands.AbelianScheme.RelativeDualSchemeFinitePresentationStatement`: over a
  quasi-separated base, the chosen dual is locally of finite presentation;
- `Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`: a smooth, proper,
  geometrically connected commutative group scheme over an algebraically closed field has
  an ample line bundle.

The module imports only these three statements and proves none of them. Each enters as
an explicit argument; nothing is assumed globally. The auxiliary declarations take only
`mumford` as an extra argument. Inspection of the final theorem reports only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The file uses no `sorry`.

## Source and provenance

The bound is the inequality `dim Pic⁰_{X/k} ≥ dim X` in the proof of Theorem (6.18) of
Edixhoven, van der Geer and Moonen, *Abelian Varieties* (printed p.96, PDF p.100;
registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`). There one takes an
ample `L`. By Lemma (2.17) the map `φ_L : X → Pic⁰` has kernel `K(L)`, which is finite,
so `dim Pic⁰ ≥ dim X`. The Lean route is local: it compares stalk dimensions at the
origin, using quasi-finiteness of the classifier at the unit. It is a transcription of the
published module `Langlands.AlgebraicGeometry.Picard.PicardOriginMumfordClassifier`, which
proves the same bound for an arbitrary universal rigidified Picard parameter
(`classifyFamily`). Here the target is the chosen Picard-zero parameter `dualScheme A hA`.
The classifying map is therefore `dualClassify`, which needs a Picard-zero class, and this
is where `mumford` is used.

All auxiliary declarations live in the namespace
`Langlands.AbelianScheme.DualOriginDimension`. The data reused from the published module
(`family`, `unitRigidified`, `inverse`, `inverseEvaluation`, `baseChangeSection_left_fst`,
`quasiFiniteAt_of_finite_fiber`, `isClosed_unit`) live in
`Langlands.AbelianScheme.PicardOriginDimension` and are not redefined.

## Imports

- `Langlands.AlgebraicGeometry.Picard.PicardOriginMumfordClassifier` (published): the
  Mumford family `family k A L` and the auxiliary lemmas listed above. Through its imports
  it also supplies `mumfordZeroParameterIso`, `FieldMumfordPoint.carrierIso`,
  `TranslationOfSmoothFamily.pullback_iso_of_tensor_trivial`,
  `GroupScheme.fibreTranslationIso`, `GroupScheme.baseChangeSection`,
  `LineBundle.isoOfPullbackIso`, `fieldLineBundleTriviality` and the published proof
  `pullbackTensorComparisonIsIso`;
- `Langlands.AlgebraicGeometry.Picard.DualScheme`: `dualScheme`, `dualClassify`,
  `dualClassify_spec`, `dualClassify_pullback`, `dualOrigin` and `dualOrigin_spec`;
- the three statement modules `MumfordBundlePicardZeroStatement`,
  `RelativeDualSchemeFinitePresentationStatement` and
  `AlgebraicallyClosedFieldAmpleExistenceStatement` (statements only);
- published proofs: `RigidifiedPullbackProofs`
  (`Langlands.SchemeModule.RigidifiedModule.pullbackCoherence`), `PicardZeroPullbackProof`
  (`picardZeroPullback`), `AlgClosedFieldAmpleTranslationStabilizerFiniteProof`
  (`algClosedFieldAmpleTranslationStabilizerFinite`), `QuasiFiniteAtStalkDimensionProof`
  (`quasiFiniteAtStalkDimension`) and `FieldSmoothClosedPointStalkDimensionProof`
  (`fieldSmoothClosedPointStalkDimension`).

## The classifier

- `mumfordClass mumford k A L : PicardZeroClasses A A.X` is the rigidified class of
  `family k A L` (`RigidifiedLineBundle.classOf`). The membership proof is
  `mumford pullbackTensorComparisonIsIso _ A (unitRigidified k A L) (inverse L)
  (inverseEvaluation L)`. This is the only use of `mumford`.
- `dualClassifier mumford k A hA L : A.X ⟶ dualScheme A hA` is
  `dualClassify A hA A.X (mumfordClass mumford k A L)`.

`one_comp_dualClassifier` shows that the unit section composed with the classifier is
`dualOrigin A hA`. By `dualClassify_pullback` (with `pullbackCoherence` and
`picardZeroPullback`), `1 ≫ dualClassifier` classifies the pullback of the Mumford class
along `1`. `dualOrigin` classifies the trivial class. The two classes agree because
`mumfordZeroParameterIso` identifies the pulled-back family with the trivial family.
`dualClassifier_unit` evaluates this at the closed point of `Spec k`: the classifier sends
the rational origin of `A` to the rational origin of the dual.

## The stabilizer lemma

`nonempty_pullback_iso_trivial`: if `σ ≫ dualClassifier = dualOrigin` for a rational
section `σ`, the relative pullback of `family k A L` along `σ` is isomorphic to the trivial
family. Indeed `dualClassify_spec` for the pulled-back class, rewritten by
`dualClassify_pullback`, `hσ` and `dualOrigin_spec`, says that both have the same rigidified
class, and `Quotient.exact` produces the isomorphism.

`translation_iso_of_pullback_iso_trivial` turns such an isomorphism `e₁` into
`(translation σ)^*L ≅ L`. The argument is the same as for `translation_iso_of_comp_classifier`
in the published module:

- forgetting the rigidification of `e₁` gives a module isomorphism `c₀`;
- with `x` the base-changed section of `σ`, `i = pullback.fst A.X.hom (𝟙 S)`,
  `t = (translation x).left`, `sy` the pullback symmetry and
  `E = t^*(i^*L) ⊗ i^*(inverse L)`, `FieldMumfordPoint.carrierIso` identifies the carrier
  of the pulled-back family with `sy.hom^*E`; with `c₀` this gives `E ≅ O`;
- `TranslationOfSmoothFamily.pullback_iso_of_tensor_trivial` gives `t^*(i^*L) ≅ i^*L`;
- `GroupScheme.fibreTranslationIso` and `LineBundle.isoOfPullbackIso` descend this along
  the isomorphism `i` to `(translation σ)^*L ≅ L`.

This lemma uses `set_option backward.isDefEq.respectTransparency false` (and its `.types`
variant) so that the base-change terms elaborate. These options affect only elaboration.
`translation_iso_of_comp_dualClassifier` combines the two lemmas.

## Topology of the fibre

- `locallyOfFiniteType_dualClassifier`: if the dual is locally of finite type, so is the
  classifier, since `dualClassifier ≫ (dualScheme A hA).hom = A.X.hom`
  (`locallyOfFiniteType_of_comp`).
- From here on `k` is algebraically closed. `isClosed_dualOrigin`: the image of the
  rational section `dualOrigin` is a closed point (`pointEquivClosedPoint`).
- `dualFiber_finite_and_closed` assumes that only finitely many rational translations
  preserve `L`. Let `Z = dualClassifier ⁻¹' {origin}`, a closed set. A closed point `z ∈ Z`
  gives a rational section of `A` (`pointOfClosedPoint`). Its composite with the classifier
  agrees with `dualOrigin` at the closed point of `Spec k`, hence equals it
  (`ext_of_apply_closedPoint_eq`). The stabilizer lemma puts the section in the
  stabilizer. This injection shows that `Z ∩ closedPoints` is finite, hence closed. Since
  `A` is Jacobson, `JacobsonSpace.closure_inter_closedPoints_eq_closure` gives
  `Z ∩ closedPoints = Z`. So `Z` is a finite set of closed points.
- `quasiFiniteAt_dualClassifier`: with `dualClassifier_unit`, the published
  `quasiFiniteAt_of_finite_fiber` shows that the classifier is quasi-finite at the origin
  of `A`.

## The conditional bound

Given `K` algebraically closed, `A`, `hA`, `g` and `hg : A.HasRelativeDimension g`:

- `finitePresentation` makes the dual locally of finite presentation, hence locally of
  finite type;
- `ample K A.toGrp inferInstance inferInstance inferInstance` gives an ample `L` on `A`
  (an abelian scheme over `Spec K` is smooth, proper and geometrically connected);
- `algClosedFieldAmpleTranslationStabilizerFinite K A L hL` says that only finitely many
  rational translations preserve `L`;
- `fieldSmoothClosedPointStalkDimension` at the closed unit point (`isClosed_unit`) rewrites
  `g` as the Krull dimension of the stalk of `A` at its origin, and `dualClassifier_unit`
  rewrites the origin of the dual as the image of that point;
- `quasiFiniteAtStalkDimension`, applied to the classifier with
  `locallyOfFiniteType_dualClassifier` and `quasiFiniteAt_dualClassifier`, gives the
  inequality.

No hypothesis beyond those displayed is used.
