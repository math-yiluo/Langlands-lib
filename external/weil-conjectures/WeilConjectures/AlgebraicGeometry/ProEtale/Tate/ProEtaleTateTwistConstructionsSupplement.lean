/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement

import all WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Filtered.Final
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistConstructions

/-! # Coefficient extension maps, the field colimit and signed Tate twists

The finite levels and integral and
rational objects are re-exported from `ProEtaleTateTwistLevels`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local irreducible] spEllPointReduction spEllPointTransition

set_option backward.isDefEq.respectTransparency false in
private theorem spIntegersMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) : IsMonHom (spIntegersMap X ℓ h) ∧
      spIntegersMap X ℓ h ≫ padicIntegersToPadicSubfield X ℓ F =
        padicIntegersToPadicSubfield X ℓ E ≫
          coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X := by
  unfold spIntegersMap
  exact (spIntegersMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spIntegersMap

private theorem spEllReduction_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllReduction X ℓ E n) := by
  dsimp only [spEllReduction]
  infer_instance

attribute [local instance] spEllReduction_isMonHom

set_option backward.isDefEq.respectTransparency false in
private theorem spEllReduction_epi (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Epi (spEllReduction X ℓ E n) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  let : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  have hq := Ideal.Quotient.mk_surjective (I := spTateEllIdeal ℓ E n)
  have hp : Epi (spEllPointReduction.{u} ℓ E n) := by
    apply (sheafToPresheaf _ _).epi_of_epi_map
    have hcomp (S : Profinite.{u}ᵒᵖ) :
        Epi ((spEllPointReduction.{u} ℓ E n).hom.app S) := by
      apply (AddCommGrpCat.epi_iff_surjective _).mpr
      intro b
      let a : C(S.unop, PadicAlgCl.integers ℓ E.1) :=
        ⟨fun t ↦ (hq (b.down t)).choose,
          (continuous_of_discreteTopology (f := fun x ↦ (hq x).choose)).comp
            b.down.continuous⟩
      refine ⟨ULift.up a, ?_⟩
      unfold spEllPointReduction
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      exact (hq (b.down t)).choose_spec
    exact @NatTrans.epi_of_epi_app _ _ _ _ _ _ _ hcomp
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) := inferInstance
  exact (upperStarFromPoint X).map_epi _

set_option backward.isDefEq.respectTransparency false in
private theorem spEllMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (n : ℕ) : spEllReduction X ℓ E n ≫ spEllMap X ℓ h n =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n := by
  unfold spEllMap
  exact (spEllMap_existsUnique X ℓ h n).exists.choose_spec

attribute [local irreducible] spEllMap

set_option backward.isDefEq.respectTransparency false in
private theorem spIntegralTwistMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) : ∀ n : ℕ, spIntegralTwistMap X ℓ h ≫
      (limit.π (spIntegralTwistSystem X ℓ F) (op n)).hom =
        (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom ≫
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) := by
  unfold spIntegralTwistMap
  exact (spIntegralTwistMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spIntegralTwistMap

private theorem spMonHom_of_epi
    {C : Type*} [Category C] [MonoidalCategory C]
    [∀ Z : C, (tensorLeft Z).PreservesEpimorphisms]
    [∀ Z : C, (tensorRight Z).PreservesEpimorphisms]
    {R B D : C} [MonObj R] [MonObj B] [MonObj D]
    (p : R ⟶ B) [IsMonHom p] [Epi p]
    (q : R ⟶ D) [IsMonHom q] (r : B ⟶ D) (h : p ≫ r = q) :
    IsMonHom r := by
  have he : Epi (p ⊗ₘ p) := by
    have : Epi (p ▷ R) := (tensorRight R).map_epi p
    have : Epi (B ◁ p) := (tensorLeft B).map_epi p
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  constructor
  · rw [← IsMonHom.one_hom p, Category.assoc, h, IsMonHom.one_hom q]
  · apply (cancel_epi (p ⊗ₘ p)).mp
    rw [← Category.assoc, ← IsMonHom.mul_hom p, Category.assoc, h, IsMonHom.mul_hom q,
      tensorHom_comp_tensorHom_assoc p p r r MonObj.mul, h]

private theorem spIntegralTwistMap_semilinear
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Mod.act (spIntegralTwist X ℓ E).X ≫ spIntegralTwistMap X ℓ h =
      (spIntegersMap X ℓ h ⊗ₘ spIntegralTwistMap X ℓ h) ≫
        Mod.act (spIntegralTwist X ℓ F).X  := by
  let : MonObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
    inferInstance
  let : MonObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X) :=
    inferInstance
  let : ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
      (spIntegralTwist X ℓ E).X :=
    (spIntegralTwist X ℓ E).mod
  let : ∀ n : ℕ,
      ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
      (spIntegralTwistLevel X ℓ E n).X := fun n ↦ (spIntegralTwistLevel X ℓ E n).mod
  let : ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X)
      (spIntegralTwist X ℓ F).X :=
    (spIntegralTwist X ℓ F).mod
  let : ∀ n : ℕ,
      ModObj (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X)
      (spIntegralTwistLevel X ℓ F n).X := fun n ↦ (spIntegralTwistLevel X ℓ F n).mod
  let : HasLimit (spIntegralTwistSystem X ℓ E) := inferInstance
  let : HasLimit (spIntegralTwistSystem X ℓ F) := inferInstance
  let pE (n : ℕᵒᵖ) : (spIntegralTwist X ℓ E).X ⟶
      (spIntegralTwistLevel X ℓ E n.unop).X :=
    (limit.π (spIntegralTwistSystem X ℓ E) n).hom
  let pF (n : ℕᵒᵖ) : (spIntegralTwist X ℓ F).X ⟶
      (spIntegralTwistLevel X ℓ F n.unop).X :=
    (limit.π (spIntegralTwistSystem X ℓ F) n).hom
  have hi : IsMonHom (spIntegersMap X ℓ h) :=
    (spIntegersMap_spec X ℓ h).1
  have he (n : ℕ) : spEllReduction X ℓ E n ≫ spEllMap X ℓ h n =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n :=
    spEllMap_spec X ℓ h n
  have hp (n : ℕ) : spIntegralTwistMap X ℓ h ≫
      pF (op n) =
      pE (op n) ≫
        (spEllMap X ℓ h n ⊗ₘ
          𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) :=
    spIntegralTwistMap_spec X ℓ h n
  have hlevel (n : ℕ) :
      Mod.act (spIntegralTwistLevel X ℓ E n).X ≫
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) =
        (spIntegersMap X ℓ h ⊗ₘ
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))) ≫
          Mod.act (spIntegralTwistLevel X ℓ F n).X := by
    let : MonObj (condensedRingObj.{u} (spEllPointRingObj.{u} ℓ E n) X) :=
      inferInstance
    let : MonObj (condensedRingObj.{u} (spEllPointRingObj.{u} ℓ F n) X) :=
      inferInstance
    have := spEllReduction_epi X ℓ E n
    have : IsMonHom (spEllMap X ℓ h n) :=
      spMonHom_of_epi (spEllReduction X ℓ E n)
        (spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n) _ (he n)
    obtain ⟨f, hf, _⟩ := spFreeTensor_linear (spEllReduction X ℓ E n)
      (spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n) (spEllMap X ℓ h n) (he n)
      (𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))
    have hl := Mod.act_hom f
    rw [hf] at hl
    set_option backward.isDefEq.respectTransparency false in
    simpa only [spIntegralTwistLevel, Mod.comap_obj_smul,
      MonoidalCategory.tensorHom_def', comp_whiskerRight, Category.assoc] using hl
  apply (isLimitOfPreserves (Mod.forget _)
    (limit.isLimit (spIntegralTwistSystem X ℓ F))).hom_ext
  intro n
  change (Mod.act (spIntegralTwist X ℓ E).X ≫ spIntegralTwistMap X ℓ h) ≫
      pF n =
    ((spIntegersMap X ℓ h ⊗ₘ spIntegralTwistMap X ℓ h) ≫
      Mod.act (spIntegralTwist X ℓ F).X) ≫
        pF n
  have hpE := Mod.act_hom (limit.π (spIntegralTwistSystem X ℓ E) n)
  have hpF := Mod.act_hom (limit.π (spIntegralTwistSystem X ℓ F) n)
  change Mod.act (spIntegralTwist X ℓ E).X ≫ _ = _ at hpE
  change Mod.act (spIntegralTwist X ℓ F).X ≫ _ = _ at hpF
  set_option backward.isDefEq.respectTransparency false in
  rw [Category.assoc, hp n.unop, ← Category.assoc,
    hpE, Category.assoc, hlevel n.unop, Category.assoc, hpF]
  set_option backward.isDefEq.respectTransparency false in
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]
  set_option backward.isDefEq.respectTransparency false in
  rw [hp n.unop]

set_option backward.isDefEq.respectTransparency true in
private theorem spExtend_map_existsUnique
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A B : C} [MonObj R] [MonObj S] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj A] [IsCommMonObj B]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (a : R ⟶ S) [IsMonHom a] (b : A ⟶ B) [IsMonHom b]
    (hab : p ≫ b = a ≫ q) (M : Mod C R) (N : Mod C S)
    (g : M.X ⟶ N.X)
    (hg : Mod.act M.X ≫ g = (a ⊗ₘ g) ≫ Mod.act N.X) :
    ∃! f : (Mod.extendScalarsObj p M).X ⟶ (Mod.extendScalarsObj q N).X,
      Mod.extendπ p M ≫ f = (b ⊗ₘ g) ≫ Mod.extendπ q N := by
  have hm : (A ◁ p ≫ MonObj.mul) ≫ b =
      (b ⊗ₘ a) ≫ (B ◁ q ≫ MonObj.mul) := by
    rw [Category.assoc, IsMonHom.mul_hom]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
    rw [hab, Category.comp_id]
  have hbal : (A ◁ p ≫ MonObj.mul) ▷ M.X ≫
        (b ⊗ₘ g) ≫ Mod.extendπ q N =
      ((α_ A R M.X).hom ≫ A ◁ Mod.act M.X) ≫
        (b ⊗ₘ g) ≫ Mod.extendπ q N := by
    calc
      _ = (((b ⊗ₘ a) ≫ (B ◁ q ≫ MonObj.mul)) ⊗ₘ g) ≫ Mod.extendπ q N := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
        rw [hm]
      _ = ((b ⊗ₘ a) ⊗ₘ g) ≫ (B ◁ q ≫ MonObj.mul) ▷ N.X ≫
          Mod.extendπ q N := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      _ = ((b ⊗ₘ a) ⊗ₘ g) ≫ (α_ B S N.X).hom ≫ B ◁ Mod.act N.X ≫
          Mod.extendπ q N := by
        rw [Mod.extendπ_condition]
        simp only [Category.assoc]
      _ = (α_ A R M.X).hom ≫ (b ⊗ₘ ((a ⊗ₘ g) ≫ Mod.act N.X)) ≫
          Mod.extendπ q N := by
        rw [associator_naturality_assoc]
        simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      _ = _ := by
        rw [← hg]
        simp only [Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp]
  refine ⟨Mod.extendDescHom p ((b ⊗ₘ g) ≫ Mod.extendπ q N) hbal,
    Mod.extendπ_extendDescHom _ _ _, ?_⟩
  intro f hf
  apply (cancel_epi (Mod.extendπ p M)).mp
  rw [hf, Mod.extendπ_extendDescHom]

private theorem spRationalTwistMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E) ≫
        spRationalTwistMap X ℓ h =
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ⊗ₘ
        spIntegralTwistMap X ℓ h) ≫
          Mod.extendπ (padicIntegersToPadicSubfield X ℓ F) (spIntegralTwist X ℓ F) := by
  unfold spRationalTwistMap
  exact (spRationalTwistMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spRationalTwistMap

/-- The identity inclusion induces the identity transition. -/
theorem spRationalTwistMap_id (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    spRationalTwistMap X ℓ (le_refl E) = 𝟙 _ := by
  have hc : coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ (le_refl E)) X =
      𝟙 _ := by
    rw [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id]
  have hi : spIntegersMap X ℓ (le_refl E) = 𝟙 _ := by
    apply (spIntegersMap_existsUnique X ℓ (le_refl E)).unique
      (spIntegersMap_spec X ℓ (le_refl E))
    exact ⟨inferInstance, by simp only [hc, Category.id_comp, Category.comp_id]⟩
  have he (n : ℕ) : spEllMap X ℓ (le_refl E) n = 𝟙 _ := by
    apply (spEllMap_existsUnique X ℓ (le_refl E) n).unique
      (spEllMap_spec X ℓ (le_refl E) n)
    simp only [hi, Category.id_comp, Category.comp_id]
  have ht : spIntegralTwistMap X ℓ (le_refl E) = 𝟙 _ := by
    apply (spIntegralTwistMap_existsUnique X ℓ (le_refl E)).unique
      (spIntegralTwistMap_spec X ℓ (le_refl E))
    intro n
    simp only [he, id_tensorHom_id]
    exact (Category.comp_id _).symm
  apply (spRationalTwistMap_existsUnique X ℓ (le_refl E)).unique
    (spRationalTwistMap_spec X ℓ (le_refl E))
  simp only [hc, ht, id_tensorHom_id, Category.id_comp]
  exact Category.comp_id _

private theorem spTensorNormalization_comp
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B D M N P U V W : C}
    (q₀ : A ⊗ M ⟶ U) (q₁ : B ⊗ N ⟶ V) (q₂ : D ⊗ P ⟶ W)
    (a : A ⟶ B) (b : B ⟶ D) (g : M ⟶ N) (h : N ⟶ P)
    (f : U ⟶ V) (k : V ⟶ W)
    (hf : q₀ ≫ f = (a ⊗ₘ g) ≫ q₁)
    (hk : q₁ ≫ k = (b ⊗ₘ h) ≫ q₂) :
    q₀ ≫ (f ≫ k) = ((a ≫ b) ⊗ₘ (g ≫ h)) ≫ q₂ := by
  rw [← Category.assoc, hf, Category.assoc, hk, ← Category.assoc,
    tensorHom_comp_tensorHom]

/-- Field-extension transitions compose. -/
theorem spRationalTwistMap_comp {E F H : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (k : F ≤ H) :
    spRationalTwistMap X ℓ (h.trans k) =
      spRationalTwistMap X ℓ h ≫ spRationalTwistMap X ℓ k := by
  let : HasLimit (spIntegralTwistSystem X ℓ E) := inferInstance
  let : HasLimit (spIntegralTwistSystem X ℓ F) := inferInstance
  let : HasLimit (spIntegralTwistSystem X ℓ H) := inferInstance
  have hc : coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ (h.trans k)) X =
      coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ≫
        coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ k) X := by
    rw [Profinite.padicSubfieldRingObjMap_comp, coefficientMap_comp]
  have hm : spIntegersMap X ℓ (h.trans k) =
      spIntegersMap X ℓ h ≫ spIntegersMap X ℓ k := by
    have := (spIntegersMap_spec X ℓ h).1
    have := (spIntegersMap_spec X ℓ k).1
    apply (spIntegersMap_existsUnique X ℓ (h.trans k)).unique
      (spIntegersMap_spec X ℓ (h.trans k))
    refine ⟨inferInstance, ?_⟩
    calc
      _ = spIntegersMap X ℓ h ≫ (spIntegersMap X ℓ k ≫
          padicIntegersToPadicSubfield X ℓ H) := Category.assoc _ _ _
      _ = _ := by rw [(spIntegersMap_spec X ℓ k).2, ← Category.assoc, (spIntegersMap_spec X ℓ h).2,
        Category.assoc, ← hc]
  have hn (n : ℕ) : spEllMap X ℓ (h.trans k) n =
      spEllMap X ℓ h n ≫ spEllMap X ℓ k n := by
    apply (spEllMap_existsUnique X ℓ (h.trans k) n).unique (spEllMap_spec X ℓ (h.trans k) n)
    rw [← Category.assoc, spEllMap_spec X ℓ h n, Category.assoc, spEllMap_spec X ℓ k n,
      ← Category.assoc, ← hm]
  have hl : spIntegralTwistMap X ℓ (h.trans k) =
      spIntegralTwistMap X ℓ h ≫ spIntegralTwistMap X ℓ k := by
    apply (spIntegralTwistMap_existsUnique X ℓ (h.trans k)).unique
      (spIntegralTwistMap_spec X ℓ (h.trans k))
    intro n
    set_option backward.isDefEq.respectTransparency false in
    rw [Category.assoc, spIntegralTwistMap_spec X ℓ k n, ← Category.assoc,
      spIntegralTwistMap_spec X ℓ h n,
      Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, ← hn n]
  apply (spRationalTwistMap_existsUnique X ℓ (h.trans k)).unique
    (spRationalTwistMap_spec X ℓ (h.trans k))
  have hh := spTensorNormalization_comp
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E))
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ F) (spIntegralTwist X ℓ F))
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ H) (spIntegralTwist X ℓ H))
    (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X)
    (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ k) X)
    (spIntegralTwistMap X ℓ h) (spIntegralTwistMap X ℓ k)
    (spRationalTwistMap X ℓ h) (spRationalTwistMap X ℓ k)
    (spRationalTwistMap_spec X ℓ h) (spRationalTwistMap_spec X ℓ k)
  set_option backward.isDefEq.respectTransparency false in
  simpa only [← hc, ← hl] using hh

attribute [local irreducible] spIntegralTwist spIntegralTwistSystem

set_option backward.isDefEq.respectTransparency true in
private theorem spExtend_semilinear
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [CategoryTheory.Limits.HasCoequalizers C]
    [∀ Z : C, CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A B : C} [MonObj R] [MonObj S] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj A] [IsCommMonObj B]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (c : A ⟶ B) [IsMonHom c] (M : Mod C R) (N : Mod C S)
    (g : M.X ⟶ N.X)
    (f : (Mod.extendScalarsObj p M).X ⟶ (Mod.extendScalarsObj q N).X)
    (hf : Mod.extendπ p M ≫ f = (c ⊗ₘ g) ≫ Mod.extendπ q N) :
    Mod.act (Mod.extendScalarsObj p M).X ≫ f =
      (c ⊗ₘ f) ≫ Mod.act (Mod.extendScalarsObj q N).X := by
  apply (cancel_epi (A ◁ Mod.extendπ p M)).mp
  rw [Mod.whiskerLeft_extendπ_smul_assoc, hf]
  calc
    _ = (α_ A A M.X).inv ≫ ((MonObj.mul ≫ c) ⊗ₘ g) ≫ Mod.extendπ q N := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (α_ A A M.X).inv ≫ (((c ⊗ₘ c) ≫ MonObj.mul) ⊗ₘ g) ≫
        Mod.extendπ q N := by rw [IsMonHom.mul_hom]
    _ = (c ⊗ₘ (c ⊗ₘ g)) ≫ (α_ B B N.X).inv ≫
        MonObj.mul ▷ N.X ≫ Mod.extendπ q N := by
      rw [associator_inv_naturality_assoc]
      simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]
    _ = (c ⊗ₘ (c ⊗ₘ g)) ≫ B ◁ Mod.extendπ q N ≫
        Mod.act (Mod.extendScalarsObj q N).X := by
      rw [Mod.whiskerLeft_extendπ_smul]
    _ = A ◁ Mod.extendπ p M ≫ (c ⊗ₘ f) ≫
        Mod.act (Mod.extendScalarsObj q N).X := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, Category.comp_id]
      rw [hf]

/-- The specified rational transitions are semilinear for the coefficient inclusions. -/
theorem spRationalTwistMap_semilinear {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    Mod.act (spRationalTwist X ℓ E).X ≫ spRationalTwistMap X ℓ h =
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ⊗ₘ
        spRationalTwistMap X ℓ h) ≫ Mod.act (spRationalTwist X ℓ F).X := by
  exact spExtend_semilinear (padicIntegersToPadicSubfield X ℓ E)
    (padicIntegersToPadicSubfield X ℓ F)
    (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X)
    (spIntegralTwist X ℓ E) (spIntegralTwist X ℓ F)
    (spIntegralTwistMap X ℓ h) (spRationalTwistMap X ℓ h)
    (spRationalTwistMap_spec X ℓ h)

/-- The specified diagram of rational twists on the small directed poset of finite fields. -/
def spRationalTwistDiagram : PadicAlgCl.FiniteIntermediateField ℓ ⥤
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} where
  obj E := (spRationalTwist X ℓ E).X
  map f := spRationalTwistMap X ℓ (leOfHom f)
  map_id E := spRationalTwistMap_id X ℓ E
  map_comp f g := spRationalTwistMap_comp X ℓ (leOfHom f) (leOfHom g)

/-- The underlying algebraic-closure twist is the sheafified abelian colimit, not a
sectionwise union without sheafification. -/
def spQbarTwistAb : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  colimit (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (spRationalTwistDiagram X ℓ)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem spColimitModule
    {C I : Type*} [Category C] [MonoidalCategory C] [Category I] [IsSifted I]
    (A M : I ⥤ C) [∀ i, MonObj (A.obj i)] [∀ i, ModObj (A.obj i) (M.obj i)]
    (cA : Cocone A) (cM : Cocone M) (hA : IsColimit cA) (hM : IsColimit cM)
    [MonObj cA.pt]
    [hι : ∀ i, @IsMonHom C _ _ (A.obj i) cA.pt inferInstance inferInstance (cA.ι.app i)]
    [PreservesColimit M (tensorLeft (𝟙_ C))]
    [PreservesColimit₂ A A (curriedTensor C)]
    [PreservesColimit₂ A M (curriedTensor C)]
    [PreservesColimit₂ (A ⊗ A) M (curriedTensor C)]
    (hsemi : ∀ {i j} (f : i ⟶ j),
      (A.map f ⊗ₘ M.map f) ≫ Mod.act (M.obj j) = Mod.act (M.obj i) ≫ M.map f) :
    ∃! a : ModObj cA.pt cM.pt,
      ∀ i, (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ a.smul =
        Mod.act (M.obj i) ≫ cM.ι.app i := by
  let ai (i : I) : A.obj i ⟶ cA.pt := cA.ι.app i
  let mi (i : I) : M.obj i ⟶ cM.pt := cM.ι.app i
  let : ∀ i, IsMonHom (ai i) := fun i ↦ hι i
  let τ : A ⊗ M ⟶ M :=
    { app i := Mod.act (M.obj i)
      naturality i j f := hsemi f }
  let c := (Cocone.precompose τ).obj cM
  let ht := hA.tensor hM
  obtain ⟨act, hact⟩ : ∃ act : cA.pt ⊗ cM.pt ⟶ cM.pt, ht.desc c = act := ⟨_, rfl⟩
  have ha (i : I) : (ai i ⊗ₘ mi i) ≫ act =
      Mod.act (M.obj i) ≫ mi i := by
    rw [← hact]
    exact ht.fac c i
  have hu : MonObj.one ▷ cM.pt ≫ act = (λ_ cM.pt).hom := by
    apply (isColimitOfPreserves (tensorLeft (𝟙_ C)) hM).hom_ext
    intro i
    change (𝟙_ C) ◁ mi i ≫ MonObj.one ▷ cM.pt ≫ act =
      (𝟙_ C) ◁ mi i ≫ (λ_ cM.pt).hom
    calc
      _ = (MonObj.one ⊗ₘ mi i) ≫ act := by
        simp only [MonoidalCategory.tensorHom_def', Category.assoc]
      _ = (MonObj.one ▷ M.obj i) ≫
          (ai i ⊗ₘ mi i) ≫ act := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          IsMonHom.one_hom, Category.id_comp]
      _ = (λ_ (M.obj i)).hom ≫ mi i := by
        rw [ha, Mod.one_act_assoc]
      _ = _ := (leftUnitor_naturality _).symm
  have hm : MonObj.mul ▷ cM.pt ≫ act =
      (α_ cA.pt cA.pt cM.pt).hom ≫ cA.pt ◁ act ≫ act := by
    apply ((hA.tensor hA).tensor hM).hom_ext
    intro i
    change ((ai i ⊗ₘ ai i) ⊗ₘ mi i) ≫
        MonObj.mul ▷ cM.pt ≫ act =
      ((ai i ⊗ₘ ai i) ⊗ₘ mi i) ≫
        (α_ cA.pt cA.pt cM.pt).hom ≫ cA.pt ◁ act ≫ act
    calc
      _ = (MonObj.mul ▷ M.obj i) ≫ (ai i ⊗ₘ mi i) ≫ act := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.comp_id, Category.id_comp, ← IsMonHom.mul_hom]
      _ = (α_ (A.obj i) (A.obj i) (M.obj i)).hom ≫
          A.obj i ◁ Mod.act (M.obj i) ≫ Mod.act (M.obj i) ≫ mi i := by
        rw [ha, Mod.mul_act_assoc]
      _ = _ := by
        rw [associator_naturality_assoc]
        simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.comp_id]
        rw [ha, ← ha]
        simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
        rw [ha]
  let a : ModObj cA.pt cM.pt :=
    { smul := act
      one_smul := hu
      mul_smul := hm }
  refine ⟨a, ?_, ?_⟩
  · intro i
    change (ai i ⊗ₘ mi i) ≫ act = Mod.act (M.obj i) ≫ mi i
    exact ha i
  intro a ha'
  apply ModObj.ext
  apply ht.hom_ext
  intro i
  exact (ha' i).trans (ha i).symm

/-- The colimit's action is uniquely determined by multiplying at a common finite field. -/
theorem spQbarTwistAction_existsUnique :
    ∃! a : ModObj (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X) (spQbarTwistAb X ℓ),
      ∀ (E F H : PadicAlgCl.FiniteIntermediateField ℓ) (hE : E ≤ H) (hF : F ≤ H),
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X ⊗ₘ
          colimit.ι (spRationalTwistDiagram X ℓ) F) ≫ a.smul =
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ hE) X ⊗ₘ
          spRationalTwistMap X ℓ hF) ≫
            Mod.act (spRationalTwist X ℓ H).X ≫
              colimit.ι (spRationalTwistDiagram X ℓ) H := by
  let A := Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X
  let M := spRationalTwistDiagram X ℓ
  let cA := (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone ℓ)
  let cM := colimit.cocone M
  let : IsSifted (PadicAlgCl.FiniteIntermediateField ℓ) := IsFiltered.isSifted
  let : ∀ E, MonObj (A.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      MonObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
    infer_instance
  let : ∀ E, ModObj (A.obj E) (M.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      ModObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
        (spRationalTwist X ℓ E).X
    exact fun E ↦ (spRationalTwist X ℓ E).mod
  let : MonObj cA.pt := by
    change MonObj (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X)
    infer_instance
  let : ∀ E, @IsMonHom _ _ _ (A.obj E) cA.pt inferInstance inferInstance
      (cA.ι.app E) := by
    intro E
    change IsMonHom
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)
    infer_instance
  have hsemi {E F : PadicAlgCl.FiniteIntermediateField ℓ} (f : E ⟶ F) :
      (A.map f ⊗ₘ M.map f) ≫ Mod.act (M.obj F) =
        Mod.act (M.obj E) ≫ M.map f :=
    (spRationalTwistMap_semilinear X ℓ (leOfHom f)).symm
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).isLeftAdjoint
  have hA : IsColimit cA := isColimitOfPreserves (upperStarFromPoint X)
    (Profinite.isColimitPadicAlgClRingObjCocone ℓ)
  obtain ⟨a, ha, hu⟩ := spColimitModule A M cA cM hA (colimit.isColimit M) hsemi
  refine ⟨a, ?_, ?_⟩
  · intro E F H hE hF
    have hcoeff : A.map (homOfLE hE) ≫ cA.ι.app H = cA.ι.app E := by
      simpa only [Category.comp_id] using cA.w (homOfLE hE)
    have htwist : M.map (homOfLE hF) ≫ cM.ι.app H = cM.ι.app F := by
      simpa only [Category.comp_id] using cM.w (homOfLE hF)
    change (cA.ι.app E ⊗ₘ cM.ι.app F) ≫ a.smul =
      (A.map (homOfLE hE) ⊗ₘ M.map (homOfLE hF)) ≫
        Mod.act (M.obj H) ≫ cM.ι.app H
    rw [← hcoeff, ← htwist, ← tensorHom_comp_tensorHom_assoc, ha H]
  · intro b hb
    apply hu
    intro E
    change (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X ⊗ₘ
      colimit.ι (spRationalTwistDiagram X ℓ) E) ≫ b.smul =
        Mod.act (spRationalTwist X ℓ E).X ≫ colimit.ι (spRationalTwistDiagram X ℓ) E
    simpa only [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id,
      spRationalTwistMap_id, id_tensorHom_id, Category.id_comp] using
      hb E E E (le_refl E) (le_refl E)

/-- Qbar_X(1), with the uniquely specified action on its sheafified colimit. -/
def spQbarTwist : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X) :=
  { X := spQbarTwistAb X ℓ
    mod := (spQbarTwistAction_existsUnique X ℓ).exists.choose }

/-- The canonical Kummer identification for finite coefficients is fixed on pure tensors. -/
theorem spFiniteKummer_existsUnique
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    ∃! k : Scheme.tateFiniteLine X ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
          (ZMod (ℓ ^ (r + 1))))) ⟶ Scheme.tateFiniteLine X ℓ A r a,
      IsIso k ∧
      ∀ (V : X.ProEt) (b : (Scheme.tateFiniteCoefficient X A).obj.obj (op V))
        (x : (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
        k.val.app (op V)
          (Scheme.tateFiniteTensor X ℓ A n
            (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
              (ZMod (ℓ ^ (r + 1))))) V b x) =
          Scheme.tateFiniteTensor X ℓ A r a V b
            ((Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
              (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
              (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x) := by
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hf⟩ := Scheme.tateTwist_finite_locallyFree X ℓ
  have hA : (ℓ ^ (r + 1) : A) = 0 := by
    have hz := congrArg a (ZMod.natCast_self (ℓ ^ (r + 1)))
    rw [map_natCast, map_zero] at hz
    simpa only [Nat.cast_pow] using hz
  obtain ⟨a', hk, _⟩ := hf A r (fun b ↦ by
    rw [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul])
  have ha : a' = a := Subsingleton.elim _ _
  subst a'
  obtain ⟨k, hiso, hk⟩ := hk n hrn
  refine ⟨k, ⟨hiso, hk⟩, ?_⟩
  intro g hg
  let := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  let := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1}
    (Scheme.tateFiniteScalar X ℓ A n
      (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
        (ZMod (ℓ ^ (r + 1)))))) (Scheme.purTwistRootsModule X ℓ n) g k
  intro V b x
  exact (hg.2 V.unop b x).trans (hk V.unop b x).symm

/-- The actual finite-coefficient Kummer identification, uniquely specified on pure tensors.
The unital quotient homomorphism a is unique, so it adds no coefficient choice. -/
def spFiniteKummer
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    Scheme.tateFiniteLine X ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
          (ZMod (ℓ ^ (r + 1))))) ⟶ Scheme.tateFiniteLine X ℓ A r a :=
  (spFiniteKummer_existsUnique X ℓ A r n hrn a).exists.choose

/-- All signed powers of an internal coefficient line, in the sectionwise module encoding.
Zero is the coefficient unit; positive degrees use tensor powers and negative
degrees use sheaf Hom into the unit. The equivalence keeps the underlying sheaf. -/
def spSignedTwist (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R) (d : ℤ) :=
  WeilConjectures.coefficientTwistLine.{u} X
    (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R)
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj L)
    d

end AlgebraicGeometry.ProEtale
