/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatComparison
import all WeilConjectures.AlgebraicGeometry.RingedLocalizationModels
import WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Acyclicity of the extended Cech tensor-augmentation cone

Source: Stacks Project, algebraization.tex, Tag 099B.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory Opposite MonoidalCategory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

section
variable {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
variable (W : MorphismProperty D) [W.IsMultiplicative] [W.RespectsIso]

private theorem tensor_augmentation_product {A B U V : D}
    (f : A ⟶ U) (g : B ⟶ V)
    (hA : W.kFlat A) (hB : W.kFlat B) (hU : W.kFlat U)
    (hf : W (A ◁ f)) (hg : W (B ◁ g)) :
    W ((A ⊗ B) ◁ (f ⊗ₘ g)) := by
  let e (X₁ X₂ Y₁ Y₂ : D) : (X₁ ⊗ X₂) ⊗ Y₁ ⊗ Y₂ ≅
      (X₁ ⊗ Y₁) ⊗ X₂ ⊗ Y₂ :=
    ⟨tensorμ X₁ X₂ Y₁ Y₂, tensorδ X₁ X₂ Y₁ Y₂,
      tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩
  apply (W.arrow_mk_iso_iff (Arrow.isoMk (e A B A B) (e A B U V)
    (tensorμ_natural_right A B f g).symm)).2
  rw [tensorHom_def]
  have hBB : W.kFlat (B ⊗ B) := ObjectProperty.prop_tensor hB hB
  have hAU : W.kFlat (A ⊗ U) := ObjectProperty.prop_tensor hA hU
  exact W.comp_mem _ _ (hBB.whiskerRight hf) (hAU.whiskerLeft hg)

omit [MonoidalCategory D] [BraidedCategory D] in
private theorem map_comp_quasiIso {E : Type*} [Category* E] [HasZeroMorphisms E]
    [CategoryWithHomology E]
    {I : Type*} {c : ComplexShape I} (F : D ⥤ HomologicalComplex E c)
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : QuasiIso (F.map f)) (hg : IsIso g) : QuasiIso (F.map (f ≫ g)) := by
  let := hf
  let := hg
  rw [F.map_comp]
  infer_instance

end

private theorem ringComplex_kflat (O : Sheaf J CommRingCat.{u}) :
    CochainComplex.IsKFlatTensor (ringedSiteRingComplex O) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (ne_of_gt hn)
  · intro n
    let := SheafOfModules.monoidalCategory O
    by_cases hn : n = 0
    · subst n
      have h := ObjectProperty.prop_unit
        (ObjectProperty.flat (A := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
      exact ((ObjectProperty.flat).prop_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm h).tensorRight
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn)).tensorRight

private theorem ringSheaf_flat (O : Sheaf J CommRingCat.{u}) :
    SheafOfModules.IsFlat
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  exact (ObjectProperty.prop_unit (ObjectProperty.flat (A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))).tensorRight

attribute [local irreducible] ringedSectionLocalization ringedSectionLocalizationPresheaf
  SheafOfModules.monoidalCategory

private theorem localizationFactor_kflat (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsKFlatTensor (ringedLocalizationTwoTerm O s) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨1, fun n hn ↦ ?_⟩
    change IsZero (ringedLocalizationTwoTermX O s n)
    simp only [ringedLocalizationTwoTermX, ite_eq_right (show n ≠ 0 by omega),
      ite_eq_right (show n ≠ 1 by omega)]
    exact isZero_zero _
  · intro n
    change SheafOfModules.IsFlat (ringedLocalizationTwoTermX O s n)
    by_cases hn : n = 0
    · subst n
      rw [ringedLocalizationTwoTermX_zero]
      let := SheafOfModules.monoidalCategory O
      exact ringSheaf_flat O
    · by_cases hn' : n = 1
      · subst n
        rw [ringedLocalizationTwoTermX_one]
        exact localization_isFlat (C := C) (J := J) O s
      · simp only [ringedLocalizationTwoTermX, ite_eq_right hn, ite_eq_right hn']
        let := SheafOfModules.monoidalCategory O
        exact (ObjectProperty.flat_of_isZero (isZero_zero _)).tensorRight

attribute [local semireducible] SheafOfModules.monoidalCategory
attribute [local instance_reducible] SheafOfModules.monoidalCategory

attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

private theorem cech_succ (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) :
    ringedExtendedCech O (r + 1) b =
      (letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
          SheafOfModules.isGrothendieckAbelian _
       letI := SheafOfModules.monoidalCategory O
       letI := SheafOfModules.symmetricCategory O
       letI := (SheafOfModules.tensorClosed O).1.some
       letI := (SheafOfModules.tensorClosed O).2.1.some
       ⟨HomologicalComplex.tensorObj (ringedLocalizationTwoTerm O (b 0))
          (ringedExtendedCech O r (fun i ↦ b i.succ)).1,
        HomologicalComplex.tensorHom (ringedLocalizationTwoTermAugmentation O (b 0))
          (ringedExtendedCech O r (fun i ↦ b i.succ)).2 ≫
          (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom⟩) := by
  rfl

private theorem cech_zero (O : Sheaf J CommRingCat.{u})
    (b : Fin 0 → (O.obj ⋙ forget CommRingCat).sections) :
    ringedExtendedCech O 0 b = ⟨ringedSiteRingComplex O, 𝟙 _⟩ := by
  rfl

attribute [local irreducible] ringedExtendedCech SheafOfModules.monoidalCategory

private theorem cech_tensor_quasiIso (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI : CategoryTheory.Limits.HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := (SheafOfModules.tensorClosed O).1.some
    letI := (SheafOfModules.tensorClosed O).2.1.some
    letI : ∀ K L : ringedSiteComplex O, HomologicalComplex.HasMapBifunctor K L
        (MonoidalCategory.curriedTensor (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) (.up ℤ) :=
      fun _ _ _ ↦ CategoryTheory.Limits.HasColimitsOfShape.has_colimit _
    (HomologicalComplex.quasiIso (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) (.up ℤ)).kFlat
        (ringedExtendedCech O r b).1 ∧
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 (ringedExtendedCech O r b).1)
      (ringedExtendedCech O r b).2
      (MonoidalCategory.curriedTensor (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) (.up ℤ)) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u, u} _
  let : ∀ K L : ringedSiteComplex O,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (.up ℤ) :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  induction r with
  | zero =>
    rw [cech_zero]
    refine ⟨(CochainComplex.isKFlatTensor_iff_kFlat _).1 (ringComplex_kflat O), ?_⟩
    change QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 (ringedSiteRingComplex O))
      (𝟙 (ringedSiteRingComplex O)) (curriedTensor A) (.up ℤ))
    change QuasiIso ((𝟙 (ringedSiteRingComplex O)) ⊗ₘ
      (𝟙 (ringedSiteRingComplex O)))
    rw [id_tensorHom_id]
    infer_instance
  | succ r ih =>
    let L := ringedLocalizationTwoTerm O (b 0)
    let K := (ringedExtendedCech O r (fun i ↦ b i.succ)).1
    let f := ringedLocalizationTwoTermAugmentation O (b 0)
    let g := (ringedExtendedCech O r (fun i ↦ b i.succ)).2
    have hL : W.kFlat L := (CochainComplex.isKFlatTensor_iff_kFlat L).1
      (localizationFactor_kflat O (b 0))
    have hK : W.kFlat K := (ih (fun i ↦ b i.succ)).1
    have hU : W.kFlat (ringedSiteRingComplex O) :=
      (CochainComplex.isKFlatTensor_iff_kFlat _).1 (ringComplex_kflat O)
    have hf : W (L ◁ f) :=
      ringed_localization_factor_tensor_augmentation_quasiIso O (b 0)
    have hg : W (K ◁ g) := (ih (fun i ↦ b i.succ)).2
    have ht : QuasiIso ((L ⊗ K) ◁ (f ⊗ₘ g)) :=
      tensor_augmentation_product W f g hL hK hU hf hg
    rw [cech_succ]
    refine ⟨ObjectProperty.prop_tensor hL hK, ?_⟩
    change QuasiIso ((((curriedTensor A).map₂CochainComplex).obj (L ⊗ K)).map _)
    dsimp only [Sigma.snd]
    -- Reuse the goal's exact tensor instances. Re-elaborating the unitor's source
    -- expands the concrete sheaf tensor unit and its chosen totalization colimits.
    -- The last local declaration is ht; the composition lemma checks its type.
    run_tac Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let mapped := target.getAppArgs[7]!
      let mapArgs := mapped.getAppArgs
      let F := mapArgs[mapArgs.size - 4]!
      let composite := mapped.appArg!
      let compArgs := composite.getAppArgs
      let f := compArgs[compArgs.size - 2]!
      let g := composite.appArg!
      let ht := (← Lean.getLCtx).foldl (fun _ decl ↦ decl.toExpr) target
      let hg ← Lean.Meta.synthInstance (← Lean.Meta.mkAppM ``IsIso #[g])
      let X := compArgs[compArgs.size - 5]!
      let Y := compArgs[compArgs.size - 4]!
      let Z := compArgs[compArgs.size - 3]!
      let proof ← Lean.Meta.withTransparency .all <|
        Lean.Meta.mkAppOptM ``map_comp_quasiIso
        #[none, none, none, none, none, none, none, none,
          some F, some X, some Y, some Z, some f, some g, some ht, some hg]
      Lean.Elab.Tactic.closeMainGoal `tensor_augmentation proof

/-- The extended Cech complex annihilates the cone of its augmentation under total tensor.

Source: Stacks Project, algebraization.tex, Tag 099B, proof of lemma-derived-completion.
(auxiliary; not a blueprint node).

Proof: write K as the ordered tensor of [O -> O[1/b_i]]. Its terms are finite sums
of flat localizations S_I. For nonempty I choose j in I. In K tensor S_I the
j-th localization differential is invertible. Its inverse, with sign (-1) to the
sum of preceding factor degrees, contracts this tensor: cross differential terms
cancel in d h + h d, and the j-th term is the identity. In cone(K -> O), cancel
the identity pair consisting of K^0 = O and the target O in degree zero. The
remaining finite positive Cech complex has a finite filtration whose graded pieces
are shifted finite sums of S_I with nonempty I. Tensoring with K makes each graded
piece contractible by the preceding formula. Induction on this finite filtration
therefore proves acyclicity of the total tensor. The cancelled identity pair is
contractible after tensoring as well. For the empty list cone(id_O) is contractible.
Zero and invertible generators, the zero ring and empty sites obey these formulas;
no exactness of infinite products is used. -/
theorem ringed_cech_tensor_augmentation_cone_acyclic (O : Sheaf J CommRingCat.{u})
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI : CategoryTheory.Limits.HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := (SheafOfModules.tensorClosed O).1.some
    letI := (SheafOfModules.tensorClosed O).2.1.some
    letI : ∀ K L : ringedSiteComplex O, HomologicalComplex.HasMapBifunctor K L
        (MonoidalCategory.curriedTensor (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) (.up ℤ) :=
      fun _ _ _ ↦ CategoryTheory.Limits.HasColimitsOfShape.has_colimit _
    (HomologicalComplex.mapBifunctor (ringedExtendedCech O r b).1
      (CochainComplex.mappingCone (ringedExtendedCech O r b).2)
      (MonoidalCategory.curriedTensor (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) (.up ℤ)).Acyclic := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u, u} _
  let : ∀ K L : ringedSiteComplex O,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (.up ℤ) :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  have hq := (cech_tensor_quasiIso O r b).2
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic _).1 hq
  exact hc.of_iso (CochainComplex.mapBifunctorMappingCone₂Iso (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2
    (MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))).symm

end CategoryTheory
