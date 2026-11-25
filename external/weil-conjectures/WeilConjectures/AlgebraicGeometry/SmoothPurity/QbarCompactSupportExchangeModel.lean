/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExtensionCompactSupportBaseChange
public import WeilConjectures.CategoryTheory.StageSystem.Morphism.PbcDescentFunctors
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory

/-!
# Compact-support base change with algebraically closed l-adic coefficients

Source: Weil conjectures blueprint main-20261015, six-functors basics,
`sk-thm-sf-pf-field/thm-cbc-qbar`, order 1992 (blueprint: def-cbc-qbar-normalized-exchange-model).

The finite-stage endpoints are fixed by their composites with integral localization,
and the exchange components by the specified completed compact-support exchange.
The conclusion includes both the overfield representative and independence relative
to an isomorphism from a representing pair to the fixed input object.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The ordinary scalar comparison transported through the specified universal
counits to the datum presentation used by compact-support exchange.
Source: blueprint main-20261015, thm-cbc-qbar, coefficient-coherence paragraph
(blueprint: def-cbc-qbar-normalized-exchange-model). -/
def cbcScalarOrdinaryIso (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    pbcEmbeddingAmbientTensor l E F i V ⋙ (pbcIntegralDatum l F).pull g ≅
      (pbcIntegralDatum l E).pull g ⋙ pbcEmbeddingAmbientTensor l E F i U :=
  Functor.isoWhiskerLeft _ (cbcDatumOrdinaryTransport (pbcIntegralDatum l F) g).symm ≪≫
    pbcScalarOrdinaryPullIso l E F i g ≪≫
      Functor.isoWhiskerRight (cbcDatumOrdinaryTransport (pbcIntegralDatum l E) g) _

/-- A presentation of completed scalar/pullback comparison with its canonical unit
normalization. Completion is a reflector and finite scalar extension preserves complete
objects, so this equation determines the comparison uniquely. These are witnesses for
that existing construction, with no choice from mere existence and no invertibility assumed.
Source: blueprint main-20261015, thm-cbc-qbar, coefficient-coherence paragraph;
prop-weil-pbc-scalar-extension, completion-unit normalization
(blueprint: def-cbc-qbar-normalized-exchange-model). -/
structure CbcCompletedScalarComparison (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {U V : Scheme.{u}} (g : U ⟶ V) where
  map : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
    pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) V ⋙ (pbcStageDatum.{u} l Ω F).completedPull g ⟶
      (pbcStageDatum.{u} l Ω E).completedPull g ⋙
        pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
          (pbcFiniteFieldInclusion l Ω h) U
  unit : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcAmbientStage l Ω V E),
    (pbcStageDatum.{u} l Ω F).ordinaryToCompleted g
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) V).obj K) ≫
        (map h).app K =
      (cbcScalarOrdinaryIso l _ _ (pbcFiniteFieldInclusion l Ω h) g).hom.app K ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) U).map
            ((pbcStageDatum.{u} l Ω E).ordinaryToCompleted g K)

/-- The inverse open scalar comparison is the mate of the canonical ordinary
scalar/pullback comparison. Its open-unit normalization is retained by `mateEquiv`.
Source: blueprint main-20261015, thm-cbc-qbar, coefficient-coherence paragraph
(blueprint: def-cbc-qbar-normalized-exchange-model). -/
def cbcScalarOpenInverse (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    pbcEmbeddingAmbientTensor l E F i U ⋙
        cbcDerivedOpenShriek (pbcIntegralDatum l F) j inferInstance ⟶
      cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance ⋙
        pbcEmbeddingAmbientTensor l E F i Z :=
  ((mateEquiv (cbcDerivedOpenAdjunction (pbcIntegralDatum l E) j)
    (cbcDerivedOpenAdjunction (pbcIntegralDatum l F) j)).symm
      (TwoSquare.mk _ _ _ _ (cbcScalarOrdinaryIso l E F i j).inv))

/-- Inverse coefficient comparison for Lg* Rp* j!, formed from the open unit mate,
the proper counit mate, and the unit-normalized completed pullback comparison.
Source: blueprint main-20261015, thm-cbc-qbar, coefficient-coherence paragraph
(blueprint: def-cbc-qbar-normalized-exchange-model). -/
def cbcScalarSourceInverse (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (pullComparison : pbcEmbeddingAmbientTensor l E F i Y ⋙
        (pbcIntegralDatum l F).completedPull g ⟶
      (pbcIntegralDatum l E).completedPull g ⋙ pbcEmbeddingAmbientTensor l E F i Y')
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (cbcCompactSupportSource g c (pbcIntegralDatum l F)).obj
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) ⟶
      (pbcEmbeddingAmbientTensor l E F i Y').obj
        ((cbcCompactSupportSource g c (pbcIntegralDatum l E)).obj K) :=
  letI := c.isOpenImmersion
  ((pbcIntegralDatum l F).completedPull g).map
      (((pbcIntegralDatum l F).push c.g).map
          ((cbcScalarOpenInverse l E F i c.i).app K) ≫
        (pbcScalarDirectImageIso l E F i c.g).inv.app
          ((cbcDerivedOpenShriek (pbcIntegralDatum l E) c.i c.isOpenImmersion).obj K)) ≫
    pullComparison.app
      (((pbcIntegralDatum l E).push c.g).obj
        ((cbcDerivedOpenShriek (pbcIntegralDatum l E) c.i c.isOpenImmersion).obj K))

/-- Inverse coefficient comparison for Rp'* j'! Lg'*, with the same three specified
mates in their target-composite order.
Source: blueprint main-20261015, thm-cbc-qbar, coefficient-coherence paragraph
(blueprint: def-cbc-qbar-normalized-exchange-model). -/
def cbcScalarTargetInverse (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X) (c' : Compactification f')
    (pullComparison : pbcEmbeddingAmbientTensor l E F i X ⋙
        (pbcIntegralDatum l F).completedPull g' ⟶
      (pbcIntegralDatum l E).completedPull g' ⋙ pbcEmbeddingAmbientTensor l E F i X')
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (cbcCompactSupportTarget g' c' (pbcIntegralDatum l F)).obj
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) ⟶
      (pbcEmbeddingAmbientTensor l E F i Y').obj
        ((cbcCompactSupportTarget g' c' (pbcIntegralDatum l E)).obj K) :=
  letI := c'.isOpenImmersion
  ((pbcIntegralDatum l F).push c'.g).map
      ((cbcDerivedOpenShriek (pbcIntegralDatum l F) c'.i c'.isOpenImmersion).map
          (pullComparison.app K) ≫
        (cbcScalarOpenInverse l E F i c'.i).app
          (((pbcIntegralDatum l E).completedPull g').obj K)) ≫
    (pbcScalarDirectImageIso l E F i c'.g).inv.app
      ((cbcDerivedOpenShriek (pbcIntegralDatum l E) c'.i c'.isOpenImmersion).obj
        (((pbcIntegralDatum l E).completedPull g').obj K))

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [QuasiCompact f]
  [IsNoetherian X] [IsNoetherian Y']
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

/-- A scalar comparison is the localization of the specified ambient inverse map,
conjugated by the integral/scalar and operation identifications. The existential
witnesses are only membership proofs, so the specification is never conditional
on extra constructibility assumptions or on a choice of coefficient comparison.
Equal coefficient fields are included.
Source: blueprint main-20261015, thm-cbc-qbar, coefficient-coherence paragraph
(blueprint: def-cbc-qbar-normalized-exchange-model). -/
def CbcScalarInverseBetaSpec
    (H : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcAmbientStage l Ω X E ⥤ pbcAmbientStage l Ω Y' E)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E) ((H E).obj K.obj))
    (P : StageSystem.Morphism
      (pbcScalarSystem l Ω X dX.out iX.out) (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (e : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcStageLocalization l Ω X E ⋙ P.Φ E =
        pbcConditionalIntegral (pbcStageDatum.{u} l Ω E) (H E) (pres E) ⋙
          pbcStageLocalization l Ω Y' E)
    (inverse : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcAmbientStage l Ω X E),
      (H F).obj ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X).obj K) ⟶
      (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) Y').obj ((H E).obj K)) :
    Prop :=
  ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (K : pbcIntegralStage l Ω X E),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω F)
        ((H F).obj ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X).obj K.obj)))
      (ht : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω F)
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) Y').obj
            ((H E).obj K.obj))),
      HEq
        ((eqToIso (e F)).inv.app ((pbcIntegralScalarExtension l Ω X dX.out iX.out h).obj K) ≫
          (P.Φ F).map ((pbcScalarIntegralComparison l Ω X dX.out iX.out h).inv.app K) ≫
          (P.β h).inv.app ((pbcStageLocalization l Ω X E).obj K) ≫
          ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map ((eqToIso (e E)).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω Y' dY'.out iY'.out h).hom.app
            ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E) (H E) (pres E)).obj K))
        ((pbcStageLocalization l Ω Y' F).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩) (inverse h K.obj)))

/-- Coherent descent data for the specified compact-support exchange. This is a
presentation of the two composites, not an alternative coefficient category.
`source` and `target` fix the rational functors on every integral object and map;
localization then fixes them on every rational map. `normalized` fixes the exchange
on every integral object, for every generating tuple of the adic ideal.
`sourceBeta` and `targetBeta` fix both scalar comparisons by localization of the
proper counit and open unit mates. The completed pullback factors are fixed by
`scalarPull.unit` and `scalarPull'.unit`, retaining their quotient augmentations.
The `CoherentExactMorphism` and `Hom` fields retain the associator, shift and
exchange-compatibility equations required by the recorded descent proposition.
No invertibility assumption is included.
Source: blueprint main-20261015, thm-cbc-qbar, first paragraph and proof steps 1--3
(blueprint: def-cbc-qbar-normalized-exchange-model). -/
structure CbcQbarExchangeModel where
  scalarPull : CbcCompletedScalarComparison l Ω g
  scalarPull' : CbcCompletedScalarComparison l Ω g'
  presSource : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
      ((cbcCompactSupportSource g c (pbcStageDatum.{u} l Ω E)).obj K.obj)
  presTarget : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
      ((cbcCompactSupportTarget g' c' (pbcStageDatum.{u} l Ω E)).obj K.obj)
  U : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out) (pbcScalarSystem l Ω Y' dY'.out iY'.out)
  V : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out) (pbcScalarSystem l Ω Y' dY'.out iY'.out)
  source : ∀ E : Padic.FiniteCoefficientFields l Ω,
    pbcStageLocalization l Ω X E ⋙ U.base.Φ E =
      pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (cbcCompactSupportSource g c (pbcStageDatum.{u} l Ω E)) (presSource E) ⋙
          pbcStageLocalization l Ω Y' E
  target : ∀ E : Padic.FiniteCoefficientFields l Ω,
    pbcStageLocalization l Ω X E ⋙ V.base.Φ E =
      pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (cbcCompactSupportTarget g' c' (pbcStageDatum.{u} l Ω E)) (presTarget E) ⋙
          pbcStageLocalization l Ω Y' E
  sourceBeta : CbcScalarInverseBetaSpec l Ω
    (fun E ↦ cbcCompactSupportSource g c (pbcStageDatum.{u} l Ω E)) presSource U.base source
    (fun {_ _} h K ↦ cbcScalarSourceInverse l _ _ (pbcFiniteFieldInclusion l Ω h) g c
      (scalarPull.map h) K)
  targetBeta : CbcScalarInverseBetaSpec l Ω
    (fun E ↦ cbcCompactSupportTarget g' c' (pbcStageDatum.{u} l Ω E)) presTarget V.base target
    (fun {_ _} h K ↦ cbcScalarTargetInverse l _ _ (pbcFiniteFieldInclusion l Ω h) g' c'
      (scalarPull'.map h) K)
  exchange : StageSystem.Morphism.Hom U.base V.base
  normalized : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (hc : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K.obj),
    HEq ((exchange.τ E).app ((pbcStageLocalization l Ω X E).obj K))
      ((pbcStageLocalization l Ω Y' E).map
        (ObjectProperty.homMk
          (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (cbcCompactSupportSource g c (pbcStageDatum.{u} l Ω E)) (presSource E)).obj K)
          (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (cbcCompactSupportTarget g' c' (pbcStageDatum.{u} l Ω E)) (presTarget E)).obj K)
          (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
            c c' gbar properSquare openSquare r a ha ⟨K.obj, hc⟩)))

end AlgebraicGeometry.Scheme
