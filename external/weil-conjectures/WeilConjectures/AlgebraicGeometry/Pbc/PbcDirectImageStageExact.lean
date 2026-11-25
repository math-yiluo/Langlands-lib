/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces
import all WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus

/-! # Normalized exact direct image at one coefficient stage
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
private theorem localizeExact
    {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject C'] [HasZeroObject D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor C' n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    [Pretriangulated C'] [Pretriangulated D']
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (Q' : C' ⥤ D') (B : C ⥤ C') (J : D ⥤ D')
    [Q.CommShift ℤ] [Q'.CommShift ℤ] [B.CommShift ℤ]
    [Q.Additive] [Q'.Additive] [B.Additive] [J.Additive]
    [B.IsTriangulated]
    (e : Q ⋙ J ≅ B ⋙ Q')
    (hQ : ∀ T : Triangle D, T ∈ distTriang D ↔
      ∃ T' : Triangle C, T' ∈ distTriang C ∧ Nonempty (T ≅ Q.mapTriangle.obj T'))
    (hQ' : ∀ T : Triangle C', T ∈ distTriang C' →
      Q'.mapTriangle.obj T ∈ distTriang D') :
    ∃! s : J.CommShift ℤ, (letI := s;
      J.IsTriangulated ∧ NatTrans.CommShift e.hom ℤ) := by
  obtain ⟨s, hs, hu⟩ := ScalarLocalization.cscLocalizedShift_exists Q W (B ⋙ Q') J e
  let := s
  have := hs
  refine ⟨s, ⟨?_, hs⟩, ?_⟩
  · constructor
    intro T hT
    obtain ⟨T', hT', ⟨eT⟩⟩ := (hQ T).1 hT
    have hB := hQ' (B.mapTriangle.obj T') (B.map_distinguished T' hT')
    let c := (Functor.mapTriangleCompIso Q J).symm.app T' ≪≫
      (Functor.mapTriangleIso e).app T' ≪≫
      (Functor.mapTriangleCompIso B Q').app T'
    exact isomorphic_distinguished _ hB _ ((J.mapTriangle.mapIso eT) ≪≫ c)
  · intro t ht
    exact hu t ht.2

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- The actual direct-image shift is fixed by its integral localization square. -/
def PbcDirectImageStageShiftSpec (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω)
    (s : (pbcDescentDirectImage l Ω f pres E).CommShift ℤ) : Prop := by
  let A := pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)
  let : A.CommShift ℤ :=
    Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
      (pbcActualModulePush f (pbcStageDatum.{u} l Ω E))
  let B := pbcConditionalIntegral (pbcStageDatum.{u} l Ω E) A (pres E)
  let eB : B ⋙ pbcStageInclusion l Ω Y E ≅ pbcStageInclusion l Ω X E ⋙ A :=
    Iso.refl _
  let : B.CommShift ℤ := Functor.CommShift.ofComp
    (F := B) (G := pbcStageInclusion l Ω Y E) eB ℤ
  let := s
  let e : pbcStageLocalization l Ω X E ⋙ pbcDescentDirectImage l Ω f pres E ≅
      B ⋙ pbcStageLocalization l Ω Y E := Iso.refl _
  exact (pbcDescentDirectImage l Ω f pres E).IsTriangulated ∧
    NatTrans.CommShift e.hom ℤ

/-- Exact direct image, with a unique shift fixed by the integral square. -/
theorem pbcDirectImageStageShift_exists (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! s : (pbcDescentDirectImage l Ω f pres E).CommShift ℤ,
      PbcDirectImageStageShiftSpec l Ω f pres E s := by
  have hX := cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) X
  have hY := cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) Y
  have := hX.1
  have := hX.2
  have := hY.1
  have := hY.2
  let A := pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)
  let : A.CommShift ℤ :=
    Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
      (pbcActualModulePush f (pbcStageDatum.{u} l Ω E))
  have : A.IsTriangulated :=
    Functor.instIsTriangulatedDerivedCategoryRightDerivedFunctor
      (pbcActualModulePush f (pbcStageDatum.{u} l Ω E))
  let B := pbcConditionalIntegral (pbcStageDatum.{u} l Ω E) A (pres E)
  let eB : B ⋙ pbcStageInclusion l Ω Y E ≅ pbcStageInclusion l Ω X E ⋙ A :=
    Iso.refl _
  let : B.CommShift ℤ := Functor.CommShift.ofComp
    (F := B) (G := pbcStageInclusion l Ω Y E) eB ℤ
  have : NatTrans.CommShift eB.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := B)
      (G := pbcStageInclusion l Ω Y E) eB ℤ
  have : B.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right eB).2 inferInstance
  let Q := pbcStageLocalization l Ω X E
  let Q' := pbcStageLocalization l Ω Y E
  let W := Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
    (pbcIntegralStage l Ω X E)
  have : Q.IsLocalization W := ScalarLocalization.pbcScalarLocalization_isLocalization
    (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcIntegralStage l Ω X E) (pbcStageUniformizer.{u} l Ω E)
  have : (pbcDescentDirectImage l Ω f pres E).Additive :=
    inferInstanceAs ((ScalarLocalization.transport
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
      (pbcStageUniformizer.{u} l Ω E) B).Additive)
  have hQ : ∀ T : Triangle (pbcStageCategory l Ω X E),
      T ∈ distTriang _ ↔ ∃ T' : Triangle (pbcIntegralStage l Ω X E),
        T' ∈ distTriang _ ∧ Nonempty (T ≅ Q.mapTriangle.obj T') :=
    (qbarStagePretriangulated_exists l Ω X E).exists.choose_spec
  have hQ' : ∀ T : Triangle (pbcIntegralStage l Ω Y E), T ∈ distTriang _ →
      Q'.mapTriangle.obj T ∈ distTriang _ := by
    intro T hT
    exact ((qbarStagePretriangulated_exists l Ω Y E).exists.choose_spec _).2
      ⟨T, hT, ⟨Iso.refl _⟩⟩
  exact localizeExact Q W Q' B
    (pbcDescentDirectImage l Ω f pres E) (Iso.refl _) hQ hQ'

/-- The uniquely normalized stage shift; its construction uses the proved
localization universal property above, which determines it uniquely. -/
@[instance_reducible] def pbcDirectImageStageCommShift (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcDescentDirectImage l Ω f pres E).CommShift ℤ :=
  (pbcDirectImageStageShift_exists l Ω f pres E).exists.choose

end AlgebraicGeometry.Scheme
