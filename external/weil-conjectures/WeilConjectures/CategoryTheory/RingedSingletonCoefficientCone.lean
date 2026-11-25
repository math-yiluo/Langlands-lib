/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality

/-! # The normalized singleton Koszul coefficient cone

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

local instance instIsGrothendieckAbelianRingedSingletonCoefficientCone :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.isGrothendieckAbelian _
local instance instMonoidalCategoryRingedSingletonCoefficientCone :
    MonoidalCategory (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.monoidalCategory O
local instance instSymmetricCategoryRingedSingletonCoefficientCone :
    SymmetricCategory (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.symmetricCategory O
local instance instMonoidalPreadditiveRingedSingletonCoefficientCone :
    MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).1
local instance instMonoidalClosedRingedSingletonCoefficientCone : MonoidalClosed (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).2.1

attribute [local irreducible] homComplexFunctor

private def doubleConeHom {A : Type*} [Category A] [Abelian A] {X Y : A} (f : X ⟶ Y) :
    HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0) ⟶
      CochainComplex.mappingCone ((HomologicalComplex.single A (.up ℤ) 0).map f) :=
  HomologicalComplex.mkHomFromDouble (by decide) (by decide)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
      (CochainComplex.mappingCone.inl _).v 0 (-1) (by decide))
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv ≫
      (CochainComplex.mappingCone.inr _).f 0)
    (by
      rw [Category.assoc, CochainComplex.mappingCone.inl_v_d _ 0 (-1) 1
        (by decide) (by decide)]
      simp [HomologicalComplex.single_map_f_self])
    (by
      intro k hk
      simp)

private def doubleConeIso {A : Type*} [Category A] [Abelian A] {X Y : A} (f : X ⟶ Y) :
    HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0) ≅
      CochainComplex.mappingCone ((HomologicalComplex.single A (.up ℤ) 0).map f) := by
  let g := doubleConeHom f
  have hg : ∀ n : ℤ, IsIso (g.f n) := by
    intro n
    by_cases h : n = -1
    · subst n
      let gi := (CochainComplex.mappingCone.fst
        ((HomologicalComplex.single A (.up ℤ) 0).map f)).1.v (-1) 0 (by decide) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫
        (HomologicalComplex.doubleXIso₀ f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).inv
      refine ⟨⟨gi, ?_, ?_⟩⟩
      · simp [g, gi, doubleConeHom]
      · apply CochainComplex.mappingCone.ext_from _ 0 (-1) (by decide)
        · simp [g, gi, doubleConeHom]
        · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y (-1)
            (by decide)).eq_of_src
    · by_cases h' : n = 0
      · subst n
        let gi := (CochainComplex.mappingCone.snd
          ((HomologicalComplex.single A (.up ℤ) 0).map f)).v 0 0 (by decide) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom ≫
          (HomologicalComplex.doubleXIso₁ f
            (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).inv
        refine ⟨⟨gi, ?_, ?_⟩⟩
        · simp [g, gi, doubleConeHom]
        · apply CochainComplex.mappingCone.ext_from _ 1 0 (by decide)
          · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X 1
              (by decide)).eq_of_src
          · simp [g, gi, doubleConeHom]
      · exact (HomologicalComplex.isZero_double_X f (by decide) n h h').isIso
          ((CochainComplex.mappingCone.isZero_X_iff _ n).mpr
            ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X (n + 1) (by omega),
              HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y n h'⟩) _
  letI := hg
  letI := HomologicalComplex.Hom.isIso_of_components g
  exact asIso g

private theorem doubleConeIso_hom {A : Type*} [Category A] [Abelian A]
    {X Y : A} (f : X ⟶ Y) : (doubleConeIso f).hom = doubleConeHom f := rfl

attribute [local irreducible] doubleConeIso

private theorem basis_rightUnit (K : ringedSiteComplex O)
    (x : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      K.X 0) :
    (MonoidalCategory.leftUnitor
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
      tensorHom x (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
      CochainComplex.ιMapBifunctor K (ringedSiteRingComplex O) (curriedTensor _)
        0 0 0 (by omega) ≫ (ringedKoszulRightUnitIso O K).hom.f 0 = x := by
  rw [← cancel_mono ((ringedKoszulRightUnitIso O K).inv.f 0)]
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f]
  change (λ_ (𝟙_ _)).inv ≫ tensorHom x
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
      HomologicalComplex.ιTensorObj K (HomologicalComplex.tensorUnit _ (.up ℤ))
        0 0 0 (by omega) ≫ 𝟙 _ = x ≫ (HomologicalComplex.rightUnitor' K).inv 0
  rw [Category.comp_id, HomologicalComplex.rightUnitor'_inv]
  simp only [tensorHom_def, Category.assoc, unitors_inv_equal]
  rw [rightUnitor_inv_naturality_assoc]
  rfl

private def singletonCoefficientIso
    (a : (O.obj ⋙ forget CommRingCat).sections)
    (d : ∀ n : ℕ, ringedNegativeKoszul O 1 (fun _ ↦ a) n ≅
      (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n)) (n : ℕ) :
    (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n) ≅
      CochainComplex.mappingCone
        ((HomologicalComplex.single _ (.up ℤ) 0).map
          (ringedKoszulScalar O a ^ (n + 1)).asHom) :=
  (d n).symm ≪≫ ringedKoszulRightUnitIso O (ringedNegativeKoszulFactor O a n) ≪≫
    doubleConeIso (ringedKoszulScalar O a ^ (n + 1)).asHom

private theorem singletonCoefficientIso_unit
    (a : (O.obj ⋙ forget CommRingCat).sections)
    (d : ∀ n : ℕ, ringedNegativeKoszul O 1 (fun _ ↦ a) n ≅
      (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n))
    (hu : ∀ n, ringedNegativeKoszulBasis O 1 (fun _ ↦ a) n ∅ 0 ≫ (d n).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
        (ringedKoszulDualUnit O 1 (fun _ ↦ a) n).f 0) (n : ℕ) :
    ringedKoszulDualUnit O 1 (fun _ ↦ a) n ≫
      (singletonCoefficientIso O a d n).hom =
        CochainComplex.mappingCone.inr
          ((HomologicalComplex.single _ (.up ℤ) 0).map
            (ringedKoszulScalar O a ^ (n + 1)).asHom) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [← cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv]
  simp only [HomologicalComplex.comp_f, singletonCoefficientIso, Iso.trans_hom,
    Iso.symm_hom]
  have hd : (d n).hom.f 0 ≫ (d n).inv.f 0 = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f ↦ f.f 0) (d n).hom_inv_id
  rw [← reassoc_of% (hu n), reassoc_of% hd]
  have hb : ringedNegativeKoszulBasis O 1 (fun _ ↦ a) n ∅ 0 ≫
      (ringedKoszulRightUnitIso O (ringedNegativeKoszulFactor O a n)).hom.f 0 =
        (HomologicalComplex.doubleXIso₁ (ringedKoszulScalar O a ^ (n + 1)).asHom
          (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).inv := by
    simpa [ringedNegativeKoszulBasis, ringedNegativeKoszulFactorBasis,
      ringedNegativeKoszul] using
      basis_rightUnit O (ringedNegativeKoszulFactor O a n)
        (ringedNegativeKoszulFactorBasis O a n 0)
  rw [← Category.assoc, hb, doubleConeIso_hom]
  simp [doubleConeHom]

attribute [local irreducible] singletonCoefficientIso

private theorem singleCone_inr_isIso
    (a : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    IsIso ((CochainComplex.mappingCone.inr
      ((HomologicalComplex.single _ (.up ℤ) 0).map
        (ringedKoszulScalar O a ^ (n + 1)).asHom)).f 0) := by
  let f := (HomologicalComplex.single _ (.up ℤ) 0).map
    (ringedKoszulScalar O a ^ (n + 1)).asHom
  change IsIso ((CochainComplex.mappingCone.inr f).f 0)
  refine ⟨⟨(CochainComplex.mappingCone.snd f).v 0 0 (add_zero 0), by simp, ?_⟩⟩
  apply CochainComplex.mappingCone.ext_from _ 1 0 (by decide)
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ 1 (by decide)).eq_of_src
  · simp

private theorem singletonCoefficientIso_transition
    (a : (O.obj ⋙ forget CommRingCat).sections)
    (d : ∀ n : ℕ, ringedNegativeKoszul O 1 (fun _ ↦ a) n ≅
      (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n))
    (hu : ∀ n, ringedNegativeKoszulBasis O 1 (fun _ ↦ a) n ∅ 0 ≫ (d n).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
        (ringedKoszulDualUnit O 1 (fun _ ↦ a) n).f 0) (n : ℕ) (j : ℤ) :
    ((ringedKoszulDualTower O 1 (fun _ ↦ a)).map
        (homOfLE (Nat.le_add_right n 1)).op).f j ≫
      (singletonCoefficientIso O a d n).hom.f j ≫
        (CochainComplex.mappingCone.snd
          ((HomologicalComplex.single _ (.up ℤ) 0).map
            (ringedKoszulScalar O a ^ (n + 1)).asHom)).v j j (add_zero j) =
      (singletonCoefficientIso O a d (n + 1)).hom.f j ≫
        (CochainComplex.mappingCone.snd
          ((HomologicalComplex.single _ (.up ℤ) 0).map
            (ringedKoszulScalar O a ^ (n + 1 + 1)).asHom)).v j j (add_zero j) := by
  by_cases hj : j = 0
  · subst j
    have hc := singletonCoefficientIso_unit O a d hu (n + 1)
    have hi := singleCone_inr_isIso O a (n + 1)
    have he : Epi ((ringedKoszulDualUnit O 1 (fun _ ↦ a) (n + 1)).f 0) := by
      have hcomp : IsIso ((ringedKoszulDualUnit O 1 (fun _ ↦ a) (n + 1)).f 0 ≫
          (singletonCoefficientIso O a d (n + 1)).hom.f 0) := by
        rw [← HomologicalComplex.comp_f, hc]
        exact hi
      have : IsIso ((ringedKoszulDualUnit O 1 (fun _ ↦ a) (n + 1)).f 0) :=
        IsIso.of_isIso_comp_right
          ((ringedKoszulDualUnit O 1 (fun _ ↦ a) (n + 1)).f 0)
          ((singletonCoefficientIso O a d (n + 1)).hom.f 0)
      exact @IsIso.epi_of_iso _ _ _ _ _ this
    rw [← cancel_epi ((ringedKoszulDualUnit O 1 (fun _ ↦ a) (n + 1)).f 0)]
    have hn : ringedKoszulDualUnit O 1 (fun _ ↦ a) (n + 1) ≫
        (ringedKoszulDualTower O 1 (fun _ ↦ a)).map
          (homOfLE (Nat.le_add_right n 1)).op =
        ringedKoszulDualUnit O 1 (fun _ ↦ a) n := by
      dsimp [ringedKoszulDualUnit, ringedKoszulDualTower]
      rw [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
        ringedKoszulProjection_naturality]
    have hn0 := congrArg (fun f ↦ f.f 0) hn
    have hc0 (m : ℕ) := congrArg (fun f ↦ f.f 0)
      (singletonCoefficientIso_unit O a d hu m)
    simp only [HomologicalComplex.comp_f] at hn0 hc0
    rw [reassoc_of% hn0, reassoc_of% (hc0 n), reassoc_of% (hc0 (n + 1))]
    simp
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ j hj).eq_of_tgt

/-- The internal dual of the singleton positive Koszul complex is the negative scalar
cone, with its normalized degree-zero unit and compatible second projections.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, the finite free dual identification.
(auxiliary; not a blueprint node).

Proof: specialize negative Koszul duality to one factor. Remove the right tensor
unit from the negative factor and identify its degrees -1 and 0 with the scalar
cone using the double-complex inclusions. The right-unitor inverse formula and
unit coherence identify the empty-subset basis with the degree-zero double basis,
so the dual unit becomes the cone inclusion. The latter is invertible in degree
zero because the shifted single-complex term is zero there. Naturality of the
dual units then determines the second projection of every successor in degree
zero. In all other degrees the projection has zero target. These categorical
identities apply also on an empty site and over the zero ring. -/
theorem ringedSingletonCoefficientCone
    (a : (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : ∀ n : ℕ,
        (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n) ≅
          CochainComplex.mappingCone
            ((HomologicalComplex.single _ (.up ℤ) 0).map
              (ringedKoszulScalar O a ^ (n + 1)).asHom),
      (∀ n, ringedKoszulDualUnit O 1 (fun _ ↦ a) n ≫ (e n).hom =
        CochainComplex.mappingCone.inr
          ((HomologicalComplex.single _ (.up ℤ) 0).map
            (ringedKoszulScalar O a ^ (n + 1)).asHom)) ∧
      (∀ (n : ℕ) (j : ℤ),
        ((ringedKoszulDualTower O 1 (fun _ ↦ a)).map
            (homOfLE (Nat.le_add_right n 1)).op).f j ≫
          (e n).hom.f j ≫
            (CochainComplex.mappingCone.snd
              ((HomologicalComplex.single _ (.up ℤ) 0).map
                (ringedKoszulScalar O a ^ (n + 1)).asHom)).v j j (add_zero j) =
          (e (n + 1)).hom.f j ≫
            (CochainComplex.mappingCone.snd
              ((HomologicalComplex.single _ (.up ℤ) 0).map
                (ringedKoszulScalar O a ^ (n + 1 + 1)).asHom)).v j j (add_zero j)) := by
  obtain ⟨d, _, hu⟩ := ringedNegativeKoszulSuccDuality O 0 (fun _ ↦ a)
  refine ⟨singletonCoefficientIso O a d, ?_, ?_⟩
  · exact singletonCoefficientIso_unit O a d hu
  · exact singletonCoefficientIso_transition O a d hu

end CategoryTheory
