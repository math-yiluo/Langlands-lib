import Langlands.Global.AdelicSpaceProperInputsStatement
import Langlands.Global.AdelicSpacePointTopologyTheorem
import Langlands.Global.AdelicSpaceProperStagesProof
import Langlands.Global.AdelicSpaceProperModelProof

/-! # Proper maps of algebraic spaces on adelic points -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

namespace AdelicSpaceSpreadProperMapReduction

/-- Proper stage maps with exact inverse images give properness for the final topology. -/
private theorem proper_of_stages {I : Type u} {A B : Type v}
    [TopologicalSpace A] [TopologicalSpace B]
    (As Bs : I → Type v) [∀ i, TopologicalSpace (As i)] [∀ i, TopologicalSpace (Bs i)]
    (f : A → B) (a : ∀ i, As i → A) (b : ∀ i, Bs i → B) (g : ∀ i, As i → Bs i)
    (hf : Continuous f) (ha : ∀ i, Continuous (a i))
    (hbi : ∀ i, Function.Injective (b i))
    (hcover : ∀ y, ∃ i z, b i z = y)
    (hcomm : ∀ i x, f (a i x) = b i (g i x))
    (hpre : ∀ i, f ⁻¹' Set.range (b i) = Set.range (a i))
    (hB : ‹TopologicalSpace B› = ⨆ i, TopologicalSpace.coinduced (b i) inferInstance)
    (hproper : ∀ i, IsProperMap (g i)) : IsProperMap f := by
  have stage_image (C : Set A) (i : I) :
      b i ⁻¹' (f '' C) = g i '' (a i ⁻¹' C) := by
    ext z
    constructor
    · rintro ⟨x, hx, hfx⟩
      have : x ∈ Set.range (a i) := by
        rw [← hpre i]
        exact ⟨z, hfx.symm⟩
      obtain ⟨w, rfl⟩ := this
      exact ⟨w, hx, hbi i ((hcomm i w).symm.trans hfx)⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨a i w, hw, hcomm i w⟩
  have closed : IsClosedMap f := by
    intro C hC
    rw [hB, isClosed_iSup_iff]
    intro i
    rw [isClosed_coinduced]
    rw [stage_image]
    exact (hproper i).isClosedMap _ (hC.preimage (ha i))
  have fibres (y : B) : IsCompact (f ⁻¹' {y}) := by
    obtain ⟨i, z, rfl⟩ := hcover y
    have fibre_eq : f ⁻¹' {b i z} = a i '' (g i ⁻¹' {z}) := by
      ext x
      constructor
      · intro hx
        have hfx : f x = b i z := hx
        have : x ∈ Set.range (a i) := by
          rw [← hpre i]
          exact ⟨z, hfx.symm⟩
        obtain ⟨w, rfl⟩ := this
        exact ⟨w, hbi i ((hcomm i w).symm.trans hfx), rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact (hcomm i w).trans (congrArg (b i) hw)
    rw [fibre_eq]
    exact ((hproper i).isCompact_preimage isCompact_singleton).image (ha i)
  exact isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hf, closed, fibres⟩

section Curve

variable (hpoints : CurvePlaceSpaceAdelePointsStatement.{u})
  (hmaps : CurvePlaceSpaceAdelePointMapsStatement.{u})
  (hstages : CurvePlaceSpaceProperStagesStatement.{u})
  (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F)) (hS : S.Nonempty)
  (X Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
  (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F S) Z)
  (gm : X ⟶ Z) (hgm : IsProperMorphism gm)

include hpoints hmaps hstages hS hX hftX hZ hftZ hgm

/-- Properness on full adelic points of a chosen proper function-field model map. -/
theorem curve_fixedModel_proper :
    @IsProperMap (CurvePlaceSpaceAdelePoints k F S X) (CurvePlaceSpaceAdelePoints k F S Z)
      (curvePlaceSpaceAdelePointTopology k F S X) (curvePlaceSpaceAdelePointTopology k F S Z)
      (RingPoints.map gm) := by
  let := curvePlaceSpaceAdelePointTopology k F S X
  let := curvePlaceSpaceAdelePointTopology k F S Z
  let : ∀ T, TopologicalSpace
      (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :=
    curvePlaceSpaceStageTopology k F S X
  let : ∀ T, TopologicalSpace
      (RingPoints (curvePlaceSIntegers k F S) Z (curvePlaceAdeleLevelOver k F S T)) :=
    curvePlaceSpaceStageTopology k F S Z
  have hpx := hpoints k F S hS X hX hftX
  have hpz := hpoints k F S hS Z hZ hftZ
  have hs := hstages k F S hS X Z hX hftX hZ hftZ gm hgm
  exact proper_of_stages
    (fun T => RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
    (fun T => RingPoints (curvePlaceSIntegers k F S) Z (curvePlaceAdeleLevelOver k F S T))
    (RingPoints.map gm) (curvePlaceSpaceStageMap k F S X) (curvePlaceSpaceStageMap k F S Z)
    (fun _ => RingPoints.map gm)
    ((hmaps k F S hS).1 X Z gm hX hftX hZ hftZ).1
    (fun T => (hpx.2.1 T).continuous) (fun T => (hpz.2.1 T).injective)
    hpz.1 (fun T x => (RingPoints.changeRing_map gm _ x).symm)
    (fun T => (hs T).2) rfl (fun T => (hs T).1)

/-- Transport a chosen model map through its commuting generic-fibre square. -/
theorem curve_spread_proper_of_model
    (Y W : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
    (f : curvePlaceSpaceGenericFiber k F S Z ≅ W) (g : Y ⟶ W)
    (hsquare : baseChangeMap (Spec.map (CommRingCat.ofHom
        (curvePlaceSIntegers k F S).subtype)) gm ≫ f.hom = e.hom ≫ g) :
    @IsProperMap (CurvePlaceSpaceFieldAdelePoints k F Y) (CurvePlaceSpaceFieldAdelePoints k F W)
      (curvePlaceSpaceSpreadTopology k F S X Y e) (curvePlaceSpaceSpreadTopology k F S Z W f)
      (RingPoints.map g) := by
  let := curvePlaceSpaceAdelePointTopology k F S X
  let := curvePlaceSpaceAdelePointTopology k F S Z
  let := curvePlaceSpaceSpreadTopology k F S X Y e
  let := curvePlaceSpaceSpreadTopology k F S Z W f
  let eX : CurvePlaceSpaceAdelePoints k F S X ≃ₜ CurvePlaceSpaceFieldAdelePoints k F Y :=
    ((curvePlaceSpaceSpreadEquiv k F S X Y e).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm
  let eZ : CurvePlaceSpaceAdelePoints k F S Z ≃ₜ CurvePlaceSpaceFieldAdelePoints k F W :=
    ((curvePlaceSpaceSpreadEquiv k F S Z W f).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm
  have hn (p : CurvePlaceSpaceAdelePoints k F S X) :
      eZ (RingPoints.map gm p) = RingPoints.map g (eX p) := by
    have hback : ∀ y, (curvePlaceSpaceGenericFiberEquiv k F S Z).symm
        (RingPoints.map (baseChangeMap _ gm) y) =
          RingPoints.map gm ((curvePlaceSpaceGenericFiberEquiv k F S X).symm y) :=
      fun y => mapSections_naturality gm _ y
    have hgen : curvePlaceSpaceGenericFiberEquiv k F S Z (RingPoints.map gm p) =
        RingPoints.map (baseChangeMap _ gm) (curvePlaceSpaceGenericFiberEquiv k F S X p) := by
      apply (curvePlaceSpaceGenericFiberEquiv k F S Z).symm.injective
      rw [hback, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    change RingPoints.map f.hom (curvePlaceSpaceGenericFiberEquiv k F S Z
      (RingPoints.map gm p)) = RingPoints.map g
        (RingPoints.map e.hom (curvePlaceSpaceGenericFiberEquiv k F S X p))
    rw [hgen, ← RingPoints.map_comp, hsquare, RingPoints.map_comp]
  have hfun : RingPoints.map g = eZ ∘ RingPoints.map gm ∘ eX.symm := by
    funext p
    simp only [Function.comp_apply, hn, eX.apply_symm_apply]
  rw [hfun]
  exact eZ.isProperMap.comp
    ((curve_fixedModel_proper hpoints hmaps hstages k F S hS X Z hX hftX hZ hftZ gm hgm).comp
      eX.symm.isProperMap)

end Curve

section NumberField

variable (hpoints : NumberFieldSpaceAdelePointsStatement.{u})
  (hmaps : NumberFieldSpaceAdelePointMapsStatement.{u})
  (hstages : NumberFieldSpaceProperStagesStatement.{u})
  (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  (X Z : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
  (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z)
  (gm : X ⟶ Z) (hgm : IsProperMorphism gm)

include hpoints hmaps hstages hX hftX hZ hftZ hgm

/-- Properness on full adelic points of a chosen proper number-field model map. -/
theorem numberField_fixedModel_proper :
    @IsProperMap (NumberFieldSpaceAdelePoints K S X) (NumberFieldSpaceAdelePoints K S Z)
      (numberFieldSpaceAdelePointTopology K S X) (numberFieldSpaceAdelePointTopology K S Z)
      (RingPoints.map gm) := by
  let := numberFieldSpaceAdelePointTopology K S X
  let := numberFieldSpaceAdelePointTopology K S Z
  let : ∀ T, TopologicalSpace
      (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :=
    numberFieldSpaceStageTopology K S X
  let : ∀ T, TopologicalSpace
      (RingPoints ((S : Set (FinitePlace K)).integer K) Z (numberFieldAdeleLevelOver K S T)) :=
    numberFieldSpaceStageTopology K S Z
  have hpx := hpoints K S X hX hftX
  have hpz := hpoints K S Z hZ hftZ
  have hs := hstages K S X Z hX hftX hZ hftZ gm hgm
  exact proper_of_stages
    (fun T => RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
    (fun T => RingPoints ((S : Set (FinitePlace K)).integer K) Z (numberFieldAdeleLevelOver K S T))
    (RingPoints.map gm) (numberFieldSpaceStageMap K S X) (numberFieldSpaceStageMap K S Z)
    (fun _ => RingPoints.map gm)
    ((hmaps K S).1 X Z gm hX hftX hZ hftZ).1
    (fun T => (hpx.2.1 T).continuous) (fun T => (hpz.2.1 T).injective)
    hpz.1 (fun T x => (RingPoints.changeRing_map gm _ x).symm)
    (fun T => (hs T).2) rfl (fun T => (hs T).1)

/-- Transport a chosen number-field model map through its generic-fibre square. -/
theorem numberField_spread_proper_of_model
    (Y W : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ Y)
    (f : numberFieldSpaceGenericFiber K S Z ≅ W) (g : Y ⟶ W)
    (hsquare : baseChangeMap (Spec.map (CommRingCat.ofHom
        ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) gm ≫ f.hom = e.hom ≫ g) :
    @IsProperMap (NumberFieldSpaceFieldAdelePoints K Y) (NumberFieldSpaceFieldAdelePoints K W)
      (numberFieldSpaceSpreadTopology K S X Y e) (numberFieldSpaceSpreadTopology K S Z W f)
      (RingPoints.map g) := by
  let := numberFieldSpaceAdelePointTopology K S X
  let := numberFieldSpaceAdelePointTopology K S Z
  let := numberFieldSpaceSpreadTopology K S X Y e
  let := numberFieldSpaceSpreadTopology K S Z W f
  let eX : NumberFieldSpaceAdelePoints K S X ≃ₜ NumberFieldSpaceFieldAdelePoints K Y :=
    ((numberFieldSpaceSpreadEquiv K S X Y e).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm
  let eZ : NumberFieldSpaceAdelePoints K S Z ≃ₜ NumberFieldSpaceFieldAdelePoints K W :=
    ((numberFieldSpaceSpreadEquiv K S Z W f).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm
  have hn (p : NumberFieldSpaceAdelePoints K S X) :
      eZ (RingPoints.map gm p) = RingPoints.map g (eX p) := by
    have hback : ∀ y, (numberFieldSpaceGenericFiberEquiv K S Z).symm
        (RingPoints.map (baseChangeMap _ gm) y) =
          RingPoints.map gm ((numberFieldSpaceGenericFiberEquiv K S X).symm y) :=
      fun y => mapSections_naturality gm _ y
    have hgen : numberFieldSpaceGenericFiberEquiv K S Z (RingPoints.map gm p) =
        RingPoints.map (baseChangeMap _ gm) (numberFieldSpaceGenericFiberEquiv K S X p) := by
      apply (numberFieldSpaceGenericFiberEquiv K S Z).symm.injective
      rw [hback, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    change RingPoints.map f.hom (numberFieldSpaceGenericFiberEquiv K S Z
      (RingPoints.map gm p)) = RingPoints.map g
        (RingPoints.map e.hom (numberFieldSpaceGenericFiberEquiv K S X p))
    rw [hgen, ← RingPoints.map_comp, hsquare, RingPoints.map_comp]
  have hfun : RingPoints.map g = eZ ∘ RingPoints.map gm ∘ eX.symm := by
    funext p
    simp only [Function.comp_apply, hn, eX.apply_symm_apply]
  rw [hfun]
  exact eZ.isProperMap.comp
    ((numberField_fixedModel_proper hpoints hmaps hstages K S X Z hX hftX hZ hftZ gm hgm).comp
      eX.symm.isProperMap)

end NumberField

end AdelicSpaceSpreadProperMapReduction

open AdelicSpaceSpreadProperMapReduction

/-- The final assembly: the topology package and the arithmetic proper-model inputs imply
exactly Conrad's Proposition 5.8, with arbitrary independently supplied models. -/
theorem adelicSpaceSpreadProperMap_of_inputs
    (htop : AdelicSpacePointTopologyStatement.{u})
    (hinputs : AdelicSpaceProperInputsStatement.{u}) :
    AdelicSpaceSpreadProperMapStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S U hS hU X Z hX hftX hZ hftZ Y W e f g hg
    obtain ⟨T, M, N, hT, hM, hftM, hN, hftN, eT, fT, gm, hgm, hsquare⟩ :=
      hinputs.2.1 k F S U hS hU X Z hX hftX hZ hftZ Y W e f g hg
    have h₁ := (htop.1.2.2.2 k F).2 S T hS hT X M hX hftX hM hftM Y e eT
    have h₂ := (htop.1.2.2.2 k F).2 U T hU hT Z N hZ hftZ hN hftN W f fT
    rw [h₁, h₂]
    exact curve_spread_proper_of_model htop.1.1 htop.1.2.1 hinputs.1.1
      k F T hT M N hM hftM hN hftN gm hgm Y W eT fT g hsquare
  · intro K _ _ S U X Z hX hftX hZ hftZ Y W e f g hg
    obtain ⟨T, M, N, hM, hftM, hN, hftN, eT, fT, gm, hgm, hsquare⟩ :=
      hinputs.2.2 K S U X Z hX hftX hZ hftZ Y W e f g hg
    have h₁ := (htop.2.2.2.2 K).2 S T X M hX hftX hM hftM Y e eT
    have h₂ := (htop.2.2.2.2 K).2 U T Z N hZ hftZ hN hftN W f fT
    rw [h₁, h₂]
    exact numberField_spread_proper_of_model htop.2.1 htop.2.2.1 hinputs.1.2
      K T M N hM hftM hN hftN gm hgm Y W eT fT g hsquare

/-- With the published topology theorem, only the two arithmetic proper-map inputs remain. -/
theorem adelicSpaceSpreadProperMap_of_arithmeticInputs
    (hstages : AdelicSpaceProperStagesStatement.{u})
    (hmodel : AdelicSpaceProperModelStatement.{u}) :
    AdelicSpaceSpreadProperMapStatement.{u} :=
  adelicSpaceSpreadProperMap_of_inputs adelicSpacePointTopology ⟨hstages, hmodel⟩

/-- With the published topology and stage theorems, only proper model replacement remains. -/
theorem adelicSpaceSpreadProperMap_of_properModel
    (hmodel : AdelicSpaceProperModelStatement.{u}) :
    AdelicSpaceSpreadProperMapStatement.{u} :=
  adelicSpaceSpreadProperMap_of_arithmeticInputs adelicSpaceProperStages hmodel

/-- Conrad's Proposition 5.8 for the published adelic topologies in both characteristics. -/
theorem adelicSpaceSpreadProperMap : AdelicSpaceSpreadProperMapStatement.{u} :=
  adelicSpaceSpreadProperMap_of_properModel adelicSpaceProperModel

end Langlands.Global
