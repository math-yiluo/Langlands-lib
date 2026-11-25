/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemCommonStageCones

/-! # Common-stage cone triangles and their isomorphism closure

The recorded generic commonStageCone and CommonStageDistinguished constructions
are reused, with their literal cone object and all three specified arrows. This
module supplies only their missing specialization to the coefficient
category and its normalized rational triangulation.

## References

* Stacks Tag 05R6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe r w u v
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

-- Compare the concrete tensor-Hom model with the existing Verdier localization.
private noncomputable def stageRationalComparison
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.inductionOn with
    | tmul a f =>
      induction g using TensorProduct.inductionOn with
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [ScalarLocalization.composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem stageLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (ScalarLocalization.localization R C p).IsLocalization
      (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let F := stageRationalComparison R C p
  have : F.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : F.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : F.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : F.IsEquivalence := {}
  let Q := ScalarLocalization.localization R C p
  have fac : Q ⋙ F ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, F, ScalarLocalization.localization, stageRationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
      (Rationalization.W M C) Q F.asEquivalence.symm
      (Functor.isoWhiskerRight fac.symm F.inv ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft Q F.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

private theorem stagePretriangulated_ext
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] (a b : Pretriangulated D)
    (h : a.distinguishedTriangles = b.distinguishedTriangles) : a = b := by
  cases a
  cases b
  cases h
  rfl

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

set_option linter.unusedVariables false in
/-- The raw rational stage has the unique pretriangulation whose triangles are
isomorphic to localized integral triangles, for the already recorded normalized
shift. -/
theorem qbarStagePretriangulated_exists (E : Padic.FiniteCoefficientFields l Qbar) :
    ∃! p : Pretriangulated (pbcStageCategory l Qbar T E),
      (fun [pInst : Pretriangulated (pbcStageCategory l Qbar T E)] ↦
        ∀ D : Triangle (pbcStageCategory l Qbar T E),
          D ∈ distTriang (pbcStageCategory l Qbar T E) ↔
            ∃ D' : Triangle (pbcIntegralStage l Qbar T E),
              D' ∈ distTriang (pbcIntegralStage l Qbar T E) ∧
                Nonempty (D ≅ (pbcStageLocalization l Qbar T E).mapTriangle.obj D'))
        (pInst := p) := by
  classical
  let C := pbcIntegralStage l Qbar T E
  let R := PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)
  let p : R := pbcStageUniformizer.{u} l Qbar E
  let M := Submonoid.powers p
  let Q := pbcStageLocalization l Qbar T E
  have : Q.IsLocalization (Rationalization.W M C) := stageLocalization R C p
  -- Use the shift directly; no comparison of HasShift structures is needed.
  let t := Triangulated.Localization.pretriangulated Q (Rationalization.W M C)
  refine ⟨t, ?_, ?_⟩
  · intro D
    change (∃ D', ∃ _ : D ≅ Q.mapTriangle.obj D', D' ∈ distTriang C) ↔ _
    constructor
    · rintro ⟨D', e, hD'⟩
      exact ⟨D', hD', ⟨e⟩⟩
    · rintro ⟨D', hD', ⟨e⟩⟩
      exact ⟨D', e, hD'⟩
  · intro t' ht'
    have heq : t'.distinguishedTriangles = t.distinguishedTriangles := by
      ext D
      exact (ht' D).trans (by
        change _ ↔ (∃ D', ∃ _ : D ≅ Q.mapTriangle.obj D', D' ∈ distTriang C)
        constructor
        · rintro ⟨D', hD', ⟨e⟩⟩
          exact ⟨D', e, hD'⟩
        · rintro ⟨D', e, hD'⟩
          exact ⟨D', hD', ⟨e⟩⟩)
    exact stagePretriangulated_ext t' t heq

/-- The stage triangles are fixed by integral images; no triangle set is arbitrary. -/
instance qbarStagePretriangulated (E : Padic.FiniteCoefficientFields l Qbar) :
    Pretriangulated (pbcStageCategory l Qbar T E) :=
  (qbarStagePretriangulated_exists l Qbar T E).exists.choose

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

end AlgebraicGeometry.Scheme
