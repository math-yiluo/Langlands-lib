/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces
import WeilConjectures.AlgebraicGeometry.Pbc.PbcDirectImageFamilyShiftCompatible

/-! # Exact structures on a normalized direct-image family
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
private theorem exactOfEquality
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) (h : F = G) (s : G.CommShift ℤ)
    (hs : letI := s; G.IsTriangulated) :
    letI : F.CommShift ℤ := h.symm ▸ s
    F.IsTriangulated := by
  subst G
  exact hs

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- The fixed actual direct-image family admits the compatible exact structures.
The input family, including its scalar coherence, is supplied independently. -/
theorem pbcDirectImageFamilyExact (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (R : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (hR : ∀ E : Padic.FiniteCoefficientFields l Ω,
      R.Φ E = pbcDescentDirectImage l Ω f pres E)
    (bR : PbcDirectImageBetaSpec l Ω f pres R) :
    ∃ C : StageSystem.CoherentExactMorphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out), C.base = R := by
  let cs : ∀ E : Padic.FiniteCoefficientFields l Ω, (R.Φ E).CommShift ℤ :=
    pbcDirectImageFamilyCommShift l Ω f pres R hR
  let := cs
  have ht : ∀ E : Padic.FiniteCoefficientFields l Ω, (R.Φ E).IsTriangulated := by
    intro E
    have hs : PbcDirectImageStageShiftSpec l Ω f pres E
        (pbcDirectImageStageCommShift l Ω f pres E) :=
      (pbcDirectImageStageShift_exists l Ω f pres E).exists.choose_spec
    exact exactOfEquality _ _ (hR E) (pbcDirectImageStageCommShift l Ω f pres E) hs.1
  have hb : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
      NatTrans.CommShift (R.β h).hom ℤ :=
    pbcDirectImageFamilyShiftCompatible l Ω f pres R hR bR
  refine ⟨{
    base := R
    additive := ?_
    commShift := cs
    betaCommShift := hb
    triangulated := ht }, rfl⟩
  intro E
  rw [hR E]
  exact inferInstanceAs ((ScalarLocalization.transport
    (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcStageUniformizer.{u} l Ω E)
    (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E))).Additive)

end AlgebraicGeometry.Scheme
