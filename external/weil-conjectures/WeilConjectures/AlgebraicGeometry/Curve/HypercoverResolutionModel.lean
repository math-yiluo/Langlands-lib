/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # An explicit injective-resolution comparison for hypercover sections

Source: Stacks Project, Hypercoverings, Tag 01H0, first proof.
(blueprint: lem-sc-hypercover-resolution-comparison).

The bicomplex is constructed by evaluating an actual resolution sheaf in every
hypercover degree. Both augmentations are explicit chain maps. Inverting the
quasi-isomorphism on homology and the canonical resolution comparison gives a
natural transformation to derived terminal sections; no arbitrary comparison
object is chosen. The first-quadrant augmentation lemma proves the required
quasi-isomorphism from injective-row acyclicity. Naturality is proved on these
chain maps, including refinement maps, and the canonical derived-functor
compatibility identifies terminal-section cohomology with etale cohomology.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicTopology

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (R : Type (u + 1)) [Ring R]

noncomputable def sectionComplexFunctor (U : FiniteSplitEtaleHypercover X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  sheafToPresheaf X.smallEtaleTopology (ModuleCat R) ⋙
    (whiskeringLeft SimplexCategory X.Etaleᵒᵖ (ModuleCat R)).obj U.simplicial.rightOp ⋙
      alternatingCofaceMapComplex (ModuleCat R)

instance (U : FiniteSplitEtaleHypercover X) : (sectionComplexFunctor R U).Additive where
  map_add := by
    intro F G f g
    ext n
    rfl

noncomputable def resolutionDoubleComplex (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u + 1} R) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip (((sectionComplexFunctor R U).mapHomologicalComplex (.up ℕ)).obj I)

noncomputable def terminalSections :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ ModuleCat.{u + 1} R :=
  sheafToPresheaf X.smallEtaleTopology (ModuleCat R) ⋙
    (evaluation X.Etaleᵒᵖ (ModuleCat R)).obj (op (⊤_ X.Etale))

instance : (terminalSections (X := X) R).Additive where
  map_add := by intros; rfl

noncomputable def sectionResolution
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  ((terminalSections R).mapHomologicalComplex (.up ℕ)).obj I

set_option backward.isDefEq.respectTransparency false in
noncomputable def restrictionToZero (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    sectionResolution R I ⟶ (resolutionDoubleComplex R U I).X 0 where
  f q := (I.X q).obj.map (terminal.from (U.simplicial.obj (op (SimplexCategory.mk 0)))).op
  comm' q r _ := (I.d q r).hom.naturality _

lemma restrictionToZero_d (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    restrictionToZero R U I ≫ (resolutionDoubleComplex R U I).d 0 1 = 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  change (I.X q).obj.map (terminal.from _).op ≫
    (∑ j : Fin 2, (-1 : ℤ) ^ j.val • (I.X q).obj.map (U.simplicial.δ j).op) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    Preadditive.comp_add, Preadditive.comp_neg, ← Functor.map_comp, ← op_comp,
    terminal.comp_from]
  exact add_neg_cancel _

set_option backward.isDefEq.respectTransparency false in
noncomputable def resolutionAugmentation (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    sectionResolution R I ⟶ (resolutionDoubleComplex R U I).total (.up ℕ) where
  f q := (restrictionToZero R U I).f q ≫
    (resolutionDoubleComplex R U I).ιTotal (.up ℕ) 0 q q (by simp)
  comm' q r h := by
    have hr : q + 1 = r := h
    subst r
    let D := resolutionDoubleComplex R U I
    let a := restrictionToZero R U I
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
      q (q + 1) (by simp [Nat.add_comm]),
      D.d₂_eq (.up ℕ) 0 (by simp : (ComplexShape.up ℕ).Rel q (q + 1)) (q + 1) (by simp)]
    have hz := congrArg (fun f ↦ f.f q) (restrictionToZero_d R U I)
    change (restrictionToZero R U I).f q ≫ (D.d 0 1).f q = 0 at hz
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := rfl
    have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := by
      change (-1 : ℤˣ) ^ 0 = 1
      exact pow_zero _
    simp only [hs₁, hs₂, one_smul, ← Category.assoc,
      hz, zero_comp, zero_add]
    rw [a.comm q (q + 1)]

set_option backward.isDefEq.respectTransparency false in
noncomputable def bottomInclusion (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (I : InjectiveResolution F) :
    (sectionComplexFunctor R U).obj F ⟶
      (resolutionDoubleComplex R U I.cocomplex).total (.up ℕ) where
  f p := ((sectionComplexFunctor R U).map (I.ι.f 0)).f p ≫
    (resolutionDoubleComplex R U I.cocomplex).ιTotal (.up ℕ) p 0 p (by simp)
  comm' p r h := by
    have hr : p + 1 = r := h
    subst r
    let D := resolutionDoubleComplex R U I.cocomplex
    let a : (sectionComplexFunctor R U).obj F ⟶
        (sectionComplexFunctor R U).obj (I.cocomplex.X 0) :=
      (sectionComplexFunctor R U).map (I.ι.f 0)
    have hz : a ≫ ((sectionComplexFunctor R U).map (I.cocomplex.d 0 1)) = 0 := by
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
        ((sectionComplexFunctor R U).map (I.cocomplex.d 0 1)).f p) ≫ _) = 0
      rw [hz', zero_comp, smul_zero]
    rw [hz'', add_zero]
    exact congrArg (fun f ↦ f ≫
      D.ιTotal (.up ℕ) (p + 1) 0 (p + 1) (by simp)) (a.comm p (p + 1))

noncomputable def sectionAugmentation (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (CochainComplex.single₀ (ModuleCat R)).obj ((terminalSections R).obj F) ⟶
      (sectionComplexFunctor R U).obj F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨F.obj.map (terminal.from _).op, by
      change F.obj.map (terminal.from _).op ≫
        (∑ j : Fin 2, (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op) = 0
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
        neg_one_zsmul, Preadditive.comp_add, Preadditive.comp_neg,
        ← Functor.map_comp, ← op_comp, terminal.comp_from]
      exact add_neg_cancel _⟩

lemma resolutionAugmentation_quasiIso
    (hrow : ∀ (U : FiniteSplitEtaleHypercover X)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)),
      Injective F → QuasiIso (sectionAugmentation R U F))
    (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (I : InjectiveResolution F) :
    QuasiIso (resolutionAugmentation R U I.cocomplex) := by
  apply HomologicalComplex₂.quasiIso_of_column_augmentation
    (resolutionDoubleComplex R U I.cocomplex) (sectionResolution R I.cocomplex)
    (restrictionToZero R U I.cocomplex) (restrictionToZero_d R U I.cocomplex)
    (resolutionAugmentation R U I.cocomplex) (fun _ ↦ rfl)
  intro n
  exact hrow U (I.cocomplex.X n) inferInstance

noncomputable def resolutionMap (U : FiniteSplitEtaleHypercover X)
    {I J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ}
    (φ : I ⟶ J) :
    (resolutionDoubleComplex R U I).total (.up ℕ) ⟶
      (resolutionDoubleComplex R U J).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map
      (((sectionComplexFunctor R U).mapHomologicalComplex (.up ℕ)).map φ)) (.up ℕ)

set_option backward.isDefEq.respectTransparency false in
lemma resolutionAugmentation_naturality (U : FiniteSplitEtaleHypercover X)
    {I J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ}
    (φ : I ⟶ J) :
    ((terminalSections R).mapHomologicalComplex (.up ℕ)).map φ ≫
        resolutionAugmentation R U J =
      resolutionAugmentation R U I ≫ resolutionMap R U φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, resolutionAugmentation, Category.assoc,
    resolutionMap, HomologicalComplex₂.ιTotal_map]
  have hh := congrArg (fun f ↦ f ≫
    (resolutionDoubleComplex R U J).ιTotal (.up ℕ) 0 n n (by simp))
    ((φ.f n).hom.naturality (terminal.from _).op).symm
  simp only [Category.assoc] at hh
  convert hh using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
lemma bottomInclusion_naturality (U : FiniteSplitEtaleHypercover X)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (f : F ⟶ G) (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (sectionComplexFunctor R U).map f ≫ bottomInclusion R U J =
      bottomInclusion R U I ≫ resolutionMap R U φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, bottomInclusion, Category.assoc,
    resolutionMap, HomologicalComplex₂.ιTotal_map]
  have h := congrArg (fun g ↦ ((sectionComplexFunctor R U).map g).f n) hφ
  have hh := congrArg (fun g ↦ g ≫
    (resolutionDoubleComplex R U J.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)) h.symm
  simp only [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc] at hh
  convert hh using 1 <;> rfl

noncomputable def derivedSingleIso (q : ℕ) :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) 0 ⋙
        Etale.cohomology (ModuleCat.{u + 1} R) X (q : ℤ) ≅
      (terminalSections R).rightDerived q := by
  let G := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let E := terminalSections (X := X) R
  let e : G ≅ E := Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal
  let e' : G.rightDerived q ≅ E.rightDerived q :=
    { hom := NatTrans.rightDerived e.hom q
      inv := NatTrans.rightDerived e.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id,
        NatTrans.rightDerived_id] }
  exact (isoWhiskerRight
    (isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) 0)
      G.rightDerivedFunctorPlusCompatibility.symm)
    (DerivedCategory.homologyFunctor (ModuleCat R) (q : ℤ))) ≪≫
    G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q ≪≫ e'

noncomputable def totalComparisonAt (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation R U I.cocomplex)] (q : ℕ) :
    ((resolutionDoubleComplex R U I.cocomplex).total (.up ℕ)).homology q ⟶
      ((terminalSections R).rightDerived q).obj F :=
  CategoryTheory.inv
    (HomologicalComplex.homologyMap (resolutionAugmentation R U I.cocomplex) q) ≫
    (I.isoRightDerivedObj (terminalSections R) q).inv

instance (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation R U I.cocomplex)] (q : ℕ) :
    IsIso (totalComparisonAt R U I q) := by dsimp [totalComparisonAt]; infer_instance

noncomputable def comparisonAt (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation R U I.cocomplex)] (q : ℕ) :
    ((sectionComplexFunctor R U).obj F).homology q ⟶
      ((terminalSections R).rightDerived q).obj F :=
  HomologicalComplex.homologyMap (bottomInclusion R U I) q ≫
    CategoryTheory.inv (HomologicalComplex.homologyMap (resolutionAugmentation R U I.cocomplex) q) ≫
    (I.isoRightDerivedObj (terminalSections R) q).inv

set_option backward.isDefEq.respectTransparency false in
lemma comparisonAt_naturality (U : FiniteSplitEtaleHypercover X)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    [QuasiIso (resolutionAugmentation R U I.cocomplex)]
    [QuasiIso (resolutionAugmentation R U J.cocomplex)]
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    HomologicalComplex.homologyMap ((sectionComplexFunctor R U).map f) q ≫
        comparisonAt R U J q =
      comparisonAt R U I q ≫ ((terminalSections R).rightDerived q).map f := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} R) (.up ℕ) q
  have : IsIso (H.map (resolutionAugmentation R U I.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation R U I.cocomplex) q))
  have : IsIso (H.map (resolutionAugmentation R U J.cocomplex)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      (resolutionAugmentation R U J.cocomplex) q))
  have hb := congrArg (fun g ↦ H.map g) (bottomInclusion_naturality R U f I J φ hφ)
  have ha := congrArg (fun g ↦ H.map g) (resolutionAugmentation_naturality R U φ)
  simp only [Functor.map_comp] at hb ha
  have hi : H.map (resolutionMap R U φ) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation R U J.cocomplex)) =
    CategoryTheory.inv (H.map (resolutionAugmentation R U I.cocomplex)) ≫
      H.map (((terminalSections R).mapHomologicalComplex (.up ℕ)).map φ) := by
    rw [← cancel_epi (H.map (resolutionAugmentation R U I.cocomplex))]
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← ha, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change H.map ((sectionComplexFunctor R U).map f) ≫
      (H.map (bottomInclusion R U J) ≫
        CategoryTheory.inv (H.map (resolutionAugmentation R U J.cocomplex)) ≫
        (J.isoRightDerivedObj (terminalSections R) q).inv) =
    (H.map (bottomInclusion R U I) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation R U I.cocomplex)) ≫
      (I.isoRightDerivedObj (terminalSections R) q).inv) ≫
        ((terminalSections R).rightDerived q).map f
  simp only [Category.assoc]
  rw [InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ]
  change H.map ((sectionComplexFunctor R U).map f) ≫ H.map (bottomInclusion R U J) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation R U J.cocomplex)) ≫ _ =
    H.map (bottomInclusion R U I) ≫
      CategoryTheory.inv (H.map (resolutionAugmentation R U I.cocomplex)) ≫
      H.map (((terminalSections R).mapHomologicalComplex (.up ℕ)).map φ) ≫ _
  rw [← Category.assoc, ← Category.assoc, hb]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ H.map (bottomInclusion R U I) ≫ k ≫
      (J.isoRightDerivedObj (terminalSections R) q).inv) hi

noncomputable def comparisonNat
    (hrow : ∀ (U : FiniteSplitEtaleHypercover X)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)),
      Injective F → QuasiIso (sectionAugmentation R U F))
    (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    cohomologyFunctor (ModuleCat.{u + 1} R) U q ⟶ (terminalSections R).rightDerived q where
  app F := by
    have := resolutionAugmentation_quasiIso R hrow U (injectiveResolution F)
    exact comparisonAt R U (injectiveResolution F) q
  naturality {F G} f := by
    have := resolutionAugmentation_quasiIso R hrow U (injectiveResolution F)
    have := resolutionAugmentation_quasiIso R hrow U (injectiveResolution G)
    exact comparisonAt_naturality R U f _ _
      (InjectiveResolution.desc f _ _) (InjectiveResolution.desc_commutes_zero f _ _) q

set_option backward.isDefEq.respectTransparency false in
attribute [irreducible] resolutionDoubleComplex

end AlgebraicGeometry.FiniteSplitEtaleHypercover
