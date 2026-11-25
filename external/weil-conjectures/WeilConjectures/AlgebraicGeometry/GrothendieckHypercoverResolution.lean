/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # An explicit injective-resolution comparison for hypercover sections

Source: Stacks Project, Hypercoverings, Tag 01H0, first proof.
(auxiliary; not a blueprint node).

The bicomplex is constructed by evaluating an actual resolution sheaf in every
hypercover degree. Both augmentations are explicit chain maps. Inverting the
quasi-isomorphism on homology and the canonical resolution comparison gives a
natural transformation to derived terminal sections; no arbitrary comparison
object is chosen. The first-quadrant augmentation lemma proves the required
quasi-isomorphism from injective-row acyclicity. Naturality is proved on these
chain maps, including refinement maps. The canonical injective-resolution computation
identifies its target with
classical right-derived terminal sections.
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicTopology

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- The alternating coface section complex `F(U₀) → F(U₁) → ⋯` of a sheaf on a hypercover. -/
noncomputable def sectionComplexFunctor (U : FiniteSplitEtaleHypercover X) :
    Sheaf X.smallEtaleTopology A ⥤
      CochainComplex A ℕ :=
  sheafToPresheaf X.smallEtaleTopology A ⋙
    (whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).obj U.simplicial.rightOp ⋙
      alternatingCofaceMapComplex A

instance (U : FiniteSplitEtaleHypercover X) : (sectionComplexFunctor A U).Additive where
  map_add := by
    intro F G f g
    ext n
    rfl

/-- The double complex obtained by applying the hypercover section complex to every term of a
cochain complex of sheaves. -/
noncomputable def resolutionDoubleComplex (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip (((sectionComplexFunctor A U).mapHomologicalComplex (.up ℕ)).obj I)

/-- Sections over the terminal object of the small étale site. -/
noncomputable def terminalSections :
    Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf X.smallEtaleTopology A ⋙
    (evaluation X.Etaleᵒᵖ A).obj (op (⊤_ X.Etale))

instance : (terminalSections (X := X) A).Additive where
  map_add := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The augmentation of the hypercover section complex by the terminal sections, given in
degree zero by restriction along `U₀ ⟶ ⊤`. -/
noncomputable def sectionAugmentation (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) :
    (CochainComplex.single₀ A).obj ((terminalSections A).obj F) ⟶
      (sectionComplexFunctor A U).obj F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨F.obj.map (terminal.from _).op, by
      simp only [sectionComplexFunctor, Functor.comp_obj, whiskeringLeft_obj_obj,
        alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
        CochainComplex.of.d, eqToHom_refl, Category.comp_id,
        AlternatingCofaceMapComplex.objD]
      change F.obj.map (terminal.from _).op ≫
        (∑ j : Fin 2, (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op) = 0
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
        neg_one_zsmul, Preadditive.comp_add, Preadditive.comp_neg,
        ← Functor.map_comp, ← op_comp, terminal.comp_from]
      exact add_neg_cancel _⟩

/-- Terminal sections of a cochain complex of sheaves. -/
noncomputable def sectionResolution
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    CochainComplex A ℕ :=
  ((terminalSections A).mapHomologicalComplex (.up ℕ)).obj I

set_option backward.isDefEq.respectTransparency false in
/-- Restriction from terminal sections to the degree-zero column of the double complex. -/
noncomputable def restrictionToZero (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    sectionResolution A I ⟶ (resolutionDoubleComplex A U I).X 0 where
  f q := (I.X q).obj.map (terminal.from (U.simplicial.obj (op (SimplexCategory.mk 0)))).op
  comm' q r _ := (I.d q r).hom.naturality _

omit [IsGrothendieckAbelian.{u + 1} A] in
lemma restrictionToZero_d (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    restrictionToZero A U I ≫ (resolutionDoubleComplex A U I).d 0 1 = 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  simp only [restrictionToZero, resolutionDoubleComplex, HomologicalComplex₂.flip,
    Functor.mapHomologicalComplex]
  simpa only [sectionAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    HomologicalComplex.single_obj_d, zero_comp] using
      (sectionAugmentation A U (I.X q)).comm 0 1

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation of the total complex by the terminal sections of the resolution. -/
noncomputable def resolutionAugmentation (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    sectionResolution A I ⟶ (resolutionDoubleComplex A U I).total (.up ℕ) where
  f q := (restrictionToZero A U I).f q ≫
    (resolutionDoubleComplex A U I).ιTotal (.up ℕ) 0 q q (by simp)
  comm' q r h := by
    have hr : q + 1 = r := h
    subst r
    let D := resolutionDoubleComplex A U I
    let a := restrictionToZero A U I
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
      q (q + 1) (by simp [Nat.add_comm]),
      D.d₂_eq (.up ℕ) 0 (by simp : (ComplexShape.up ℕ).Rel q (q + 1)) (q + 1) (by simp)]
    have hz := congrArg (fun f ↦ f.f q) (restrictionToZero_d A U I)
    change (restrictionToZero A U I).f q ≫ (D.d 0 1).f q = 0 at hz
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := rfl
    have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := by
      change (-1 : ℤˣ) ^ 0 = 1
      exact pow_zero _
    simp only [hs₁, hs₂, one_smul, ← Category.assoc,
      hz, zero_comp, zero_add]
    rw [a.comm q (q + 1)]

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of the hypercover section complex of `F` into the total complex, induced by
the coaugmentation `F ⟶ I⁰` of an injective resolution. -/
noncomputable def bottomInclusion (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    (sectionComplexFunctor A U).obj F ⟶
      (resolutionDoubleComplex A U I.cocomplex).total (.up ℕ) where
  f p := ((sectionComplexFunctor A U).map (I.ι.f 0)).f p ≫
    (resolutionDoubleComplex A U I.cocomplex).ιTotal (.up ℕ) p 0 p (by simp)
  comm' p r h := by
    have hr : p + 1 = r := h
    subst r
    let D := resolutionDoubleComplex A U I.cocomplex
    let a : (sectionComplexFunctor A U).obj F ⟶
        (sectionComplexFunctor A U).obj (I.cocomplex.X 0) :=
      (sectionComplexFunctor A U).map (I.ι.f 0)
    have hz : a ≫ ((sectionComplexFunctor A U).map (I.cocomplex.d 0 1)) = 0 := by
      rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]
    have hz' := congrArg (fun f ↦ f.f p) hz
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz'
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel p (p + 1))
      0 (p + 1) (by simp),
      D.d₂_eq (.up ℕ) p (by simp : (ComplexShape.up ℕ).Rel 0 1) (p + 1)
        (by simp)]
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (p, 0) = 1 := rfl
    simp only [hs₁, one_smul]
    change a.f p ≫ (D.d p (p + 1)).f 0 ≫ D.ιTotal (.up ℕ) (p + 1) 0 (p + 1) _ +
      a.f p ≫ (_ • (D.X p).d 0 1 ≫ D.ιTotal (.up ℕ) p 1 (p + 1) _) = _
    simp only [← Category.assoc]
    have hz'' : a.f p ≫
        (ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (p, 0) •
          ((D.X p).d 0 1 ≫ D.ιTotal (.up ℕ) p 1 (p + 1) (by simp))) = 0 := by
      rw [Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc]
      change _ • ((a.f p ≫
        ((sectionComplexFunctor A U).map (I.cocomplex.d 0 1)).f p) ≫ _) = 0
      rw [hz', zero_comp, smul_zero]
    rw [hz'', add_zero]
    exact congrArg (fun f ↦ f ≫
      D.ιTotal (.up ℕ) (p + 1) 0 (p + 1) (by simp)) (a.comm p (p + 1))


/-- If injective sheaves have acyclic augmented hypercover rows, the total-complex augmentation
of an injective resolution is a quasi-isomorphism. -/
lemma resolutionAugmentation_quasiIso
    (hrow : ∀ (U : FiniteSplitEtaleHypercover X)
      (F : Sheaf X.smallEtaleTopology A),
      Injective F → QuasiIso (sectionAugmentation A U F))
    (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    QuasiIso (resolutionAugmentation A U I.cocomplex) := by
  apply HomologicalComplex₂.quasiIso_of_column_augmentation
    (resolutionDoubleComplex A U I.cocomplex) (sectionResolution A I.cocomplex)
    (restrictionToZero A U I.cocomplex) (restrictionToZero_d A U I.cocomplex)
    (resolutionAugmentation A U I.cocomplex) (fun _ ↦ rfl)
  intro n
  exact hrow U (I.cocomplex.X n) inferInstance

/-- The map of total complexes induced by a map of cochain complexes of sheaves. -/
noncomputable def resolutionMap (U : FiniteSplitEtaleHypercover X)
    {I J : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ}
    (φ : I ⟶ J) :
    (resolutionDoubleComplex A U I).total (.up ℕ) ⟶
      (resolutionDoubleComplex A U J).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map
      (((sectionComplexFunctor A U).mapHomologicalComplex (.up ℕ)).map φ)) (.up ℕ)

set_option backward.isDefEq.respectTransparency false in
lemma resolutionAugmentation_naturality (U : FiniteSplitEtaleHypercover X)
    {I J : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ}
    (φ : I ⟶ J) :
    ((terminalSections A).mapHomologicalComplex (.up ℕ)).map φ ≫
        resolutionAugmentation A U J =
      resolutionAugmentation A U I ≫ resolutionMap A U φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, resolutionAugmentation, Category.assoc,
    resolutionMap, HomologicalComplex₂.ιTotal_map]
  have hh := congrArg (fun f ↦ f ≫
    (resolutionDoubleComplex A U J).ιTotal (.up ℕ) 0 n n (by simp))
    ((φ.f n).hom.naturality (terminal.from _).op).symm
  simp only [Category.assoc] at hh
  convert hh using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
lemma bottomInclusion_naturality (U : FiniteSplitEtaleHypercover X)
    {F G : Sheaf X.smallEtaleTopology A}
    (f : F ⟶ G) (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (sectionComplexFunctor A U).map f ≫ bottomInclusion A U J =
      bottomInclusion A U I ≫ resolutionMap A U φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, bottomInclusion, Category.assoc,
    resolutionMap, HomologicalComplex₂.ιTotal_map]
  have h := congrArg (fun g ↦ ((sectionComplexFunctor A U).map g).f n) hφ
  have hh := congrArg (fun g ↦ g ≫
    (resolutionDoubleComplex A U J.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)) h.symm
  simp only [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc] at hh
  convert hh using 1 <;> rfl

/-- The map of hypercover section complexes induced by a refinement `U ⟶ V`. -/
noncomputable def sectionRefinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V) : sectionComplexFunctor A V ⟶ sectionComplexFunctor A U :=
  whiskerRight (whiskerLeft (sheafToPresheaf X.smallEtaleTopology A)
    ((whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).map f.rightOp))
    (alternatingCofaceMapComplex A)

/-- The map of total complexes induced by a refinement `U ⟶ V`. -/
noncomputable def totalRefinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    (resolutionDoubleComplex A V I).total (.up ℕ) ⟶
      (resolutionDoubleComplex A U I).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map
      ((NatTrans.mapHomologicalComplex (sectionRefinement A f) (.up ℕ)).app I)) (.up ℕ)

set_option backward.isDefEq.respectTransparency false in
lemma resolutionAugmentation_refinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    resolutionAugmentation A V I ≫ totalRefinement A f I = resolutionAugmentation A U I := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, resolutionAugmentation, Category.assoc,
    totalRefinement, HomologicalComplex₂.ιTotal_map]
  change (I.X n).obj.map (terminal.from _).op ≫
    (I.X n).obj.map (f.app _).op ≫ _ = (I.X n).obj.map (terminal.from _).op ≫ _
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, terminal.comp_from]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma bottomInclusion_refinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    (sectionRefinement A f).app F ≫ bottomInclusion A U I =
      bottomInclusion A V I ≫ totalRefinement A f I.cocomplex := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, bottomInclusion, Category.assoc,
    totalRefinement, HomologicalComplex₂.ιTotal_map]
  have hh := congrArg (fun g ↦ g ≫
    (resolutionDoubleComplex A U I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp))
    ((I.ι.f 0).hom.naturality (f.app (op (SimplexCategory.mk n))).op)
  simp only [Category.assoc] at hh
  convert hh using 1 <;> rfl

/-- The identification of the cohomology of the total complex with derived terminal sections. -/
noncomputable def totalComparisonAt (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation A U I.cocomplex)] (q : ℕ) :
    ((resolutionDoubleComplex A U I.cocomplex).total (.up ℕ)).homology q ⟶
      ((terminalSections A).rightDerived q).obj F :=
  CategoryTheory.inv
    (HomologicalComplex.homologyMap (resolutionAugmentation A U I.cocomplex) q) ≫
    (I.isoRightDerivedObj (terminalSections A) q).inv

instance (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation A U I.cocomplex)] (q : ℕ) :
    IsIso (totalComparisonAt A U I q) := by dsimp [totalComparisonAt]; infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma totalComparisonAt_refinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation A U I.cocomplex)]
    [QuasiIso (resolutionAugmentation A V I.cocomplex)] (q : ℕ) :
    HomologicalComplex.homologyMap (totalRefinement A f I.cocomplex) q ≫
      totalComparisonAt A U I q = totalComparisonAt A V I q := by
  let H := HomologicalComplex.homologyFunctor A (.up ℕ) q
  have : IsIso (H.map (resolutionAugmentation A U I.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation A U I.cocomplex) q))
  have : IsIso (H.map (resolutionAugmentation A V I.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation A V I.cocomplex) q))
  have ha := congrArg (fun g ↦ H.map g) (resolutionAugmentation_refinement A f I.cocomplex)
  simp only [Functor.map_comp] at ha
  change H.map (totalRefinement A f I.cocomplex) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A U I.cocomplex)) ≫ _ =
    CategoryTheory.inv (H.map (resolutionAugmentation A V I.cocomplex)) ≫ _
  rw [← cancel_epi (H.map (resolutionAugmentation A V I.cocomplex))]
  rw [← Category.assoc, ← Category.assoc, ha]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

/-- The comparison map from hypercover cohomology to derived terminal sections in degree `q`,
through the total complex of an injective resolution. -/
noncomputable def comparisonAt (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation A U I.cocomplex)] (q : ℕ) :
    ((sectionComplexFunctor A U).obj F).homology q ⟶
      ((terminalSections A).rightDerived q).obj F :=
  HomologicalComplex.homologyMap (bottomInclusion A U I) q ≫
    CategoryTheory.inv (HomologicalComplex.homologyMap (resolutionAugmentation A U I.cocomplex) q) ≫
    (I.isoRightDerivedObj (terminalSections A) q).inv

set_option backward.isDefEq.respectTransparency false in
lemma comparisonAt_naturality (U : FiniteSplitEtaleHypercover X)
    {F G : Sheaf X.smallEtaleTopology A} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    [QuasiIso (resolutionAugmentation A U I.cocomplex)]
    [QuasiIso (resolutionAugmentation A U J.cocomplex)]
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    HomologicalComplex.homologyMap ((sectionComplexFunctor A U).map f) q ≫
        comparisonAt A U J q =
      comparisonAt A U I q ≫ ((terminalSections A).rightDerived q).map f := by
  let H := HomologicalComplex.homologyFunctor A (.up ℕ) q
  have : IsIso (H.map (resolutionAugmentation A U I.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation A U I.cocomplex) q))
  have : IsIso (H.map (resolutionAugmentation A U J.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation A U J.cocomplex) q))
  have hb := congrArg (fun g ↦ H.map g) (bottomInclusion_naturality A U f I J φ hφ)
  have ha := congrArg (fun g ↦ H.map g) (resolutionAugmentation_naturality A U φ)
  simp only [Functor.map_comp] at hb ha
  have hi : H.map (resolutionMap A U φ) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A U J.cocomplex)) =
    CategoryTheory.inv (H.map (resolutionAugmentation A U I.cocomplex)) ≫
      H.map (((terminalSections A).mapHomologicalComplex (.up ℕ)).map φ) := by
    rw [← cancel_epi (H.map (resolutionAugmentation A U I.cocomplex))]
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← ha, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change H.map ((sectionComplexFunctor A U).map f) ≫
      (H.map (bottomInclusion A U J) ≫
        CategoryTheory.inv (H.map (resolutionAugmentation A U J.cocomplex)) ≫
        (J.isoRightDerivedObj (terminalSections A) q).inv) =
    (H.map (bottomInclusion A U I) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A U I.cocomplex)) ≫
      (I.isoRightDerivedObj (terminalSections A) q).inv) ≫
        ((terminalSections A).rightDerived q).map f
  simp only [Category.assoc]
  rw [InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ]
  change H.map ((sectionComplexFunctor A U).map f) ≫ H.map (bottomInclusion A U J) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A U J.cocomplex)) ≫ _ =
    H.map (bottomInclusion A U I) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A U I.cocomplex)) ≫
      H.map (((terminalSections A).mapHomologicalComplex (.up ℕ)).map φ) ≫ _
  rw [← Category.assoc, ← Category.assoc, hb]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ H.map (bottomInclusion A U I) ≫ k ≫
      (J.isoRightDerivedObj (terminalSections A) q).inv) hi

/-- The comparison from hypercover cohomology to derived terminal sections, natural in the
sheaf, assuming acyclicity of injective hypercover rows. -/
noncomputable def comparisonNat
    (hrow : ∀ (U : FiniteSplitEtaleHypercover X)
      (F : Sheaf X.smallEtaleTopology A),
      Injective F → QuasiIso (sectionAugmentation A U F))
    (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    cohomologyFunctor A U q ⟶ (terminalSections A).rightDerived q where
  app F := by
    have := resolutionAugmentation_quasiIso A hrow U (injectiveResolution F)
    exact comparisonAt A U (injectiveResolution F) q
  naturality {F G} f := by
    have := resolutionAugmentation_quasiIso A hrow U (injectiveResolution F)
    have := resolutionAugmentation_quasiIso A hrow U (injectiveResolution G)
    exact comparisonAt_naturality A U f _ _
      (InjectiveResolution.desc f _ _) (InjectiveResolution.desc_commutes_zero f _ _) q

set_option backward.isDefEq.respectTransparency false in
/-- The comparison maps are compatible with refinement maps of hypercovers. -/
lemma comparisonNat_refinement
    (hrow : ∀ (U : FiniteSplitEtaleHypercover X)
      (F : Sheaf X.smallEtaleTopology A),
      Injective F → QuasiIso (sectionAugmentation A U F))
    {U V : FiniteSplitEtaleHypercover X} (f : U.Refinement V) (q : ℕ) :
    cohomologyRefinement A f q ≫ comparisonNat A hrow U q =
      comparisonNat A hrow V q := by
  apply NatTrans.ext
  funext F
  let I := injectiveResolution F
  have := resolutionAugmentation_quasiIso A hrow U I
  have := resolutionAugmentation_quasiIso A hrow V I
  let H := HomologicalComplex.homologyFunctor A (.up ℕ) q
  have : IsIso (H.map (resolutionAugmentation A U I.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation A U I.cocomplex) q))
  have : IsIso (H.map (resolutionAugmentation A V I.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation A V I.cocomplex) q))
  have hb := congrArg (fun g ↦ H.map g) (bottomInclusion_refinement A f I)
  have ha := congrArg (fun g ↦ H.map g) (resolutionAugmentation_refinement A f I.cocomplex)
  simp only [Functor.map_comp] at hb ha
  have hi : H.map (totalRefinement A f I.cocomplex) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A U I.cocomplex)) =
      CategoryTheory.inv (H.map (resolutionAugmentation A V I.cocomplex)) := by
    rw [← cancel_epi (H.map (resolutionAugmentation A V I.cocomplex))]
    simp only [← Category.assoc, ha, IsIso.hom_inv_id]
  change H.map ((sectionRefinement A f).app F) ≫ H.map (bottomInclusion A U I) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A U I.cocomplex)) ≫ _ =
    H.map (bottomInclusion A V I) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation A V I.cocomplex)) ≫ _
  rw [← Category.assoc, ← Category.assoc, hb]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ H.map (bottomInclusion A V I) ≫ k ≫
      (I.isoRightDerivedObj (terminalSections A) q).inv) hi

-- Keep the sectionwise bicomplex opaque to instance search in downstream proofs.
attribute [irreducible] resolutionDoubleComplex

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
