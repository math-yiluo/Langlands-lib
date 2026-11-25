/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.CategoryTheory.Preadditive.Comma
public import WeilConjectures.CategoryTheory.Sites.FramedLift.FramedLifts
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Coordinates on relative degree-one cocycles

## References

* Stacks Project, Tag 03AJ (relative injective-resolution refinement)
* Stacks Project, Tag 0G71
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable (T : Scheme.{u}) (U : T.Etale)
  (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)

/-- Coordinate isomorphism, before changing the sign of the open summand. -/
noncomputable def relativeDegreeIso (n : ℕ) :
    (relativeSectionComplex T U I).X (n + 1) ≅
      AddCommGrpCat.of ((I.X (n + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))) ×
        (I.X n).obj.obj (op U)) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (relativeSectionRestriction T U I)
      ((n : ℤ) + 1 + -1) (n + 1) (by change (n : ℤ) + 1 + -1 + 1 = (n : ℤ) + 1; omega) ≪≫
    biprod.mapIso
      (HomologicalComplex.extendXIso _ _ (by simp :
        ComplexShape.embeddingUpNat.f (n + 1) = (n : ℤ) + 1))
      (HomologicalComplex.extendXIso _ _ (by simp :
        ComplexShape.embeddingUpNat.f n = (n : ℤ) + 1 + -1)) ≪≫
    AddCommGrpCat.biprodIsoProd _ _

/-- The first coordinate of a relative cochain. -/
noncomputable def relativeFst (n : ℕ) :
    (relativeSectionComplex T U I).X (n + 1) ⟶
      (I.X (n + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  (relativeDegreeIso T U I n).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)

/-- The unsigned second coordinate of a relative cochain. -/
noncomputable def relativeSnd (n : ℕ) :
    (relativeSectionComplex T U I).X (n + 1) ⟶ (I.X n).obj.obj (op U) :=
  (relativeDegreeIso T U I n).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)

private lemma relativeFst_eq (n : ℕ) :
    relativeFst T U I n =
      HomologicalComplex.homotopyCofiber.fstX (relativeSectionRestriction T U I)
        ((n : ℤ) + 1 + -1) (n + 1) (by change _ + 1 = _; omega) ≫
      (HomologicalComplex.extendXIso _ _ (by simp :
        ComplexShape.embeddingUpNat.f (n + 1) = (n : ℤ) + 1)).hom := by
  unfold relativeFst relativeDegreeIso
  simp only [Iso.trans_hom, Category.assoc]
  erw [← AddCommGrpCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc,
    biprod.mapIso_hom, biprod.map_fst]
  rfl

private lemma cofiber_snd {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (i j : ℤ) (h : i + 1 = j) :
    (HomologicalComplex.homotopyCofiber.XIsoBiprod r i j h).hom ≫ biprod.snd =
      HomologicalComplex.homotopyCofiber.sndX r i := by
  subst j
  apply HomologicalComplex.homotopyCofiber.ext_from_X r (i + 1) i rfl <;> simp

private lemma relativeSnd_eq (n : ℕ) :
    relativeSnd T U I n =
      HomologicalComplex.homotopyCofiber.sndX (relativeSectionRestriction T U I)
        ((n : ℤ) + 1 + -1) ≫
      (HomologicalComplex.extendXIso _ _ (by simp :
        ComplexShape.embeddingUpNat.f n = (n : ℤ) + 1 + -1)).hom := by
  unfold relativeSnd relativeDegreeIso
  simp only [Iso.trans_hom, Category.assoc]
  erw [← AddCommGrpCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc,
    biprod.mapIso_hom, biprod.map_snd]
  rw [← Category.assoc, cofiber_snd]

/-- The first coordinate of the relative differential is the ordinary differential. -/
theorem relative_d_fst :
    (relativeSectionComplex T U I).d 1 2 ≫ relativeFst T U I 1 =
      relativeFst T U I 0 ≫ (I.d 1 2).hom.app (op (Scheme.Etale.mk (𝟙 T))) := by
  rw [relativeFst_eq, relativeFst_eq]
  simp only [relativeSectionComplex, CochainComplex.shiftFunctor_obj_d',
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  change (-HomologicalComplex.homotopyCofiber.d (relativeSectionRestriction T U I) 0 1) ≫
      (HomologicalComplex.homotopyCofiber.fstX _ 1 2 rfl ≫ _) = _
  rw [← Category.assoc, Preadditive.neg_comp,
    HomologicalComplex.homotopyCofiber.d_fstX _ 0 1 2 rfl rfl, neg_neg,
    Category.assoc]
  rw [Category.assoc]
  apply congrArg (HomologicalComplex.homotopyCofiber.fstX _ 0 1 rfl ≫ ·)
  dsimp only [relativeSections]
  erw [HomologicalComplex.extend_d_eq _ _ (rfl :
    ComplexShape.embeddingUpNat.f 1 = (1 : ℤ)) (rfl :
      ComplexShape.embeddingUpNat.f 2 = (2 : ℤ))]
  simp

private lemma restriction_f (n : ℕ) :
    (relativeSectionRestriction T U I).f (n : ℤ) ≫
        (HomologicalComplex.extendXIso _ _ (rfl :
          ComplexShape.embeddingUpNat.f n = (n : ℤ))).hom =
      (HomologicalComplex.extendXIso _ _ (rfl :
        ComplexShape.embeddingUpNat.f n = (n : ℤ))).hom ≫
        (I.X n).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op := by
  dsimp only [relativeSectionRestriction]
  erw [HomologicalComplex.extendMap_f _ _ (rfl :
    ComplexShape.embeddingUpNat.f n = (n : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The open coordinate has differential minus restriction minus the open differential. -/
theorem relative_d_snd :
    (relativeSectionComplex T U I).d 1 2 ≫ relativeSnd T U I 1 =
      -(relativeFst T U I 0 ≫
          (I.X 1).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op +
        relativeSnd T U I 0 ≫ (I.d 0 1).hom.app (op U)) := by
  rw [relativeSnd_eq, relativeSnd_eq, relativeFst_eq]
  simp only [relativeSectionComplex, CochainComplex.shiftFunctor_obj_d',
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  change (-HomologicalComplex.homotopyCofiber.d (relativeSectionRestriction T U I) 0 1) ≫
      (HomologicalComplex.homotopyCofiber.sndX _ 1 ≫ _) = _
  rw [← Category.assoc, Preadditive.neg_comp,
    HomologicalComplex.homotopyCofiber.d_sndX _ 0 1 rfl,
    Preadditive.neg_comp, Preadditive.add_comp]
  apply congrArg Neg.neg
  apply congrArg₂ (· + ·)
  · erw [Category.assoc, restriction_f]
    rfl
  · simp only [Category.assoc]
    apply congrArg (HomologicalComplex.homotopyCofiber.sndX _ 0 ≫ ·)
    dsimp only [relativeSections]
    erw [HomologicalComplex.extend_d_eq _ _ (rfl :
      ComplexShape.embeddingUpNat.f 0 = (0 : ℤ)) (rfl :
        ComplexShape.embeddingUpNat.f 1 = (1 : ℤ))]
    simp

private lemma relative_coordinates_ext (n : ℕ)
    {x y : (relativeSectionComplex T U I).X (n + 1)}
    (h₁ : relativeFst T U I n x = relativeFst T U I n y)
    (h₂ : relativeSnd T U I n x = relativeSnd T U I n y) : x = y := by
  apply (AddCommGrpCat.mono_iff_injective (relativeDegreeIso T U I n).hom).1 inferInstance
  exact Prod.ext h₁ h₂

private lemma relative_coordinates_inv (n : ℕ)
    (a : (I.X (n + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X n).obj.obj (op U)) :
    relativeFst T U I n ((relativeDegreeIso T U I n).inv (a, b)) = a ∧
      relativeSnd T U I n ((relativeDegreeIso T U I n).inv (a, b)) = b := by
  have hh := CategoryTheory.Iso.inv_hom_id_apply (relativeDegreeIso T U I n) (a, b)
  exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩

/-- In degree zero the negative open term is zero, leaving the global sections of I0. -/
noncomputable def relativeDegreeZeroIso :
    (relativeSectionComplex T U I).X 0 ≅
      (I.X 0).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  CochainComplex.shiftFunctorObjXIso
      (CochainComplex.mappingCone (relativeSectionRestriction T U I)) (-1) 0 (-1)
        (by simp) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod
      (relativeSectionRestriction T U I) (-1) 0 (by decide) ≪≫
    (isoBiprodZero
      (X := (relativeSections (Scheme.Etale.mk (𝟙 T)) I).X 0)
      (Y := (relativeSections U I).X (-1))
      (HomologicalComplex.isZero_extend_X _ _ (-1) (by
      intro n
      change (n : ℤ) ≠ -1
      omega))).symm ≪≫
    HomologicalComplex.extendXIso _ _ (rfl :
      ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))

/-- A relative boundary has global coordinate d(x). -/
theorem relativeBoundary_fst :
    (relativeDegreeZeroIso T U I).inv ≫ (relativeSectionComplex T U I).d 0 1 ≫
        relativeFst T U I 0 = (I.d 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) := by
  rw [relativeFst_eq]
  simp only [relativeSectionComplex, CochainComplex.shiftFunctor_obj_d',
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  change (relativeDegreeZeroIso T U I).inv ≫
    (-HomologicalComplex.homotopyCofiber.d (relativeSectionRestriction T U I) (-1) 0) ≫
      (HomologicalComplex.homotopyCofiber.fstX _ 0 1 rfl ≫ _) = _
  rw [← Category.assoc (-HomologicalComplex.homotopyCofiber.d _ (-1) 0),
    Preadditive.neg_comp, HomologicalComplex.homotopyCofiber.d_fstX _ (-1) 0 1 (by decide) rfl,
    neg_neg]
  dsimp only [relativeDegreeZeroIso, Iso.trans_inv, Iso.symm_inv, isoBiprodZero]
  simp only [Category.assoc, HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv]
  dsimp only [relativeSections]
  erw [HomologicalComplex.extend_d_eq _ _ (rfl :
    ComplexShape.embeddingUpNat.f 0 = (0 : ℤ)) (rfl :
      ComplexShape.embeddingUpNat.f 1 = (1 : ℤ))]
  simp

/-- The unsigned open coordinate of a relative boundary is minus restriction of x. -/
theorem relativeBoundary_snd :
    (relativeDegreeZeroIso T U I).inv ≫ (relativeSectionComplex T U I).d 0 1 ≫
        relativeSnd T U I 0 =
      -(I.X 0).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op := by
  rw [relativeSnd_eq]
  simp only [relativeSectionComplex, CochainComplex.shiftFunctor_obj_d',
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  change (relativeDegreeZeroIso T U I).inv ≫
    (-HomologicalComplex.homotopyCofiber.d (relativeSectionRestriction T U I) (-1) 0) ≫
      (HomologicalComplex.homotopyCofiber.sndX _ 0 ≫ _) = _
  rw [← Category.assoc (-HomologicalComplex.homotopyCofiber.d _ (-1) 0),
    Preadditive.neg_comp,
    HomologicalComplex.homotopyCofiber.d_sndX _ (-1) 0 (by decide)]
  dsimp only [relativeDegreeZeroIso, Iso.trans_inv, Iso.symm_inv, isoBiprodZero]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_add,
    Preadditive.add_comp, Category.assoc,
    HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv]
  erw [restriction_f T U I 0]
  simp

/-- The first differential with its codomain restricted to cycles. -/
noncomputable def resolutionLiftSequence
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (R : InjectiveResolution G) :
    ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (R.ι.f 0) (R.cocomplex.toCycles 0 1) (by
    apply (cancel_mono (R.cocomplex.iCycles 1)).1
    simp only [Category.assoc, HomologicalComplex.toCycles_i, zero_comp,
      R.ι_f_zero_comp_complex_d])

/-- Exactness identifies the cycles in degree one with the quotient of I0 by G. -/
theorem resolutionLiftSequence_shortExact
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (R : InjectiveResolution G) :
    (resolutionLiftSequence T R).ShortExact := by
  let f : resolutionLiftSequence T R ⟶
      ShortComplex.mk (R.ι.f 0) (R.cocomplex.d 0 1) R.ι_f_zero_comp_complex_d :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := R.cocomplex.iCycles 1
      comm₁₂ := by simp [resolutionLiftSequence]
      comm₂₃ := by simp [resolutionLiftSequence] }
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).2 R.exact₀
  · change Mono (R.ι.f 0)
    infer_instance
  · change Epi (R.cocomplex.toCycles 0 1)
    have : Epi (R.cocomplex.toCycles 0 1 ≫
        (R.cocomplex.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom) := by
      rw [HomologicalComplex.toCycles_cyclesIsoSc'_hom]
      exact (R.exact_succ 0).epi_toCycles
    exact (epi_comp_iff_of_isIso _ _).1 this

/-- A degree-one cocycle with its specified open lift, in a sheaf resolution. -/
noncomputable abbrev ResolutionFramedLift
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (R : InjectiveResolution G) :=
  Sheaf.Torsor.FramedLift (MorphismProperty.Over.mkIdTerminal @Etale T)
    (resolutionLiftSequence_shortExact T R) U

/-- The relative-to-absolute map is the positive first coordinate. -/
theorem relativeForget_fst :
    (relativeForgetComplex T U I).f 1 ≫
      (HomologicalComplex.extendXIso
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj I)
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 1 = 1)).hom =
      relativeFst T U I 0 := by
  rw [relativeFst_eq]
  simp only [relativeForgetComplex, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctor_map_f',
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.rightShift_coe,
    CochainComplex.HomComplex.Cochain.rightShift_v,
    CochainComplex.mappingCone.fst, CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v]
  rfl

variable {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (R : InjectiveResolution G)

/-- The signed cochain associated to a framed lift: coordinates (a,-b). -/
noncomputable def relativeFrameElement (z : ResolutionFramedLift T U R) :
    (relativeSectionComplex T U R.cocomplex).X 1 :=
  (relativeDegreeIso T U R.cocomplex 0).inv
    ((R.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1,
      -(show (R.cocomplex.X 0).obj.obj (op U) from z.2.1))

private lemma relativeFrameElement_coordinates (z : ResolutionFramedLift T U R) :
    relativeFst T U R.cocomplex 0 (relativeFrameElement T U R z) =
        (R.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1 ∧
      relativeSnd T U R.cocomplex 0 (relativeFrameElement T U R z) =
        -(show (R.cocomplex.X 0).obj.obj (op U) from z.2.1) :=
  relative_coordinates_inv T U R.cocomplex 0 _ _

private lemma frame_restriction (z : ResolutionFramedLift T U R) :
    (R.cocomplex.d 0 1).hom.app (op U) z.2.1 =
      (R.cocomplex.X 1).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op
        ((R.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1) := by
  have hv := z.2.2
  change (R.cocomplex.toCycles 0 1).hom.app (op U) z.2.1 =
    (R.cocomplex.cycles 1).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op z.1 at hv
  calc
    _ = (R.cocomplex.iCycles 1).hom.app (op U)
        ((R.cocomplex.toCycles 0 1).hom.app (op U) z.2.1) :=
      (congrArg (fun f ↦ f.hom.app (op U) z.2.1)
        (R.cocomplex.toCycles_i 0 1)).symm
    _ = (R.cocomplex.iCycles 1).hom.app (op U)
        ((R.cocomplex.cycles 1).obj.map
          ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op z.1) := by rw [hv]
    _ = _ := congrArg (fun f ↦ f z.1)
      ((R.cocomplex.iCycles 1).hom.naturality
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op)

/-- The signed cochain of a framed lift is closed. -/
theorem relativeFrameElement_closed (z : ResolutionFramedLift T U R) :
    (relativeSectionComplex T U R.cocomplex).d 1 2 (relativeFrameElement T U R z) = 0 := by
  apply relative_coordinates_ext T U R.cocomplex 1
  · erw [← ConcreteCategory.comp_apply, relative_d_fst, ConcreteCategory.comp_apply,
      (relativeFrameElement_coordinates T U R z).1, map_zero]
    exact congrArg (fun f ↦ f.hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1)
      (R.cocomplex.iCycles_d 1 2)
  · erw [← ConcreteCategory.comp_apply, relative_d_snd]
    simp only [AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply,
      AddCommGrpCat.hom_add_apply,
      ConcreteCategory.comp_apply, map_zero]
    erw [(relativeFrameElement_coordinates T U R z).1,
      (relativeFrameElement_coordinates T U R z).2, map_neg, frame_restriction]
    exact neg_eq_zero.mpr (add_neg_cancel _)

/-- A framed lift, regarded as a cycle of the actual relative complex. -/
noncomputable def relativeFrameCycle (z : ResolutionFramedLift T U R) :
    (relativeSectionComplex T U R.cocomplex).cycles 1 :=
  ((relativeSectionComplex T U R.cocomplex).cyclesIsoSc' 0 1 2 (by simp) (by simp)).inv
    (((relativeSectionComplex T U R.cocomplex).sc' 0 1 2).abCyclesIso.inv
      ⟨relativeFrameElement T U R z, relativeFrameElement_closed T U R z⟩)

private lemma relativeFrameCycle_i (z : ResolutionFramedLift T U R) :
    (relativeSectionComplex T U R.cocomplex).iCycles 1 (relativeFrameCycle T U R z) =
      relativeFrameElement T U R z := by
  unfold relativeFrameCycle
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesIsoSc'_inv_iCycles]
  exact ShortComplex.abCyclesIso_inv_apply_iCycles _ _

/-- The homology class of a framed lift in the actual shifted restriction cone. -/
noncomputable def relativeFrameClass (z : ResolutionFramedLift T U R) :
    relativeCohomology T U R 1 :=
  (relativeSectionComplex T U R.cocomplex).homologyπ 1 (relativeFrameCycle T U R z)

/-- The absolute section cycle obtained by forgetting the open lift. -/
noncomputable def relativeFrameAbsoluteCycle (z : ResolutionFramedLift T U R) :
    ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
      R.cocomplex).cycles 1) :=
  (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
    R.cocomplex).extendCyclesIso ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1) |>.hom
      (HomologicalComplex.cyclesMap (relativeForgetComplex T U R.cocomplex) 1
        (relativeFrameCycle T U R z))

/-- Forgetting a framed relative cycle leaves exactly its global cocycle coordinate. -/
theorem relativeFrameAbsoluteCycle_i (z : ResolutionFramedLift T U R) :
    ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
      R.cocomplex).iCycles 1) (relativeFrameAbsoluteCycle T U R z) =
      (R.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1 := by
  unfold relativeFrameAbsoluteCycle
  erw [← ConcreteCategory.comp_apply, HomologicalComplex.extendCyclesIso_hom_iCycles,
    ← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i_assoc]
  simp only [ConcreteCategory.comp_apply]
  rw [relativeFrameCycle_i]
  erw [← ConcreteCategory.comp_apply, relativeForget_fst]
  exact (relativeFrameElement_coordinates T U R z).1

/-- The absolute homology image is represented by the displayed absolute cycle. -/
theorem relativeFrameAbsoluteCycle_class (z : ResolutionFramedLift T U R) :
    (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
      R.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1)).hom
        (HomologicalComplex.homologyMap (relativeForgetComplex T U R.cocomplex) 1
          (relativeFrameClass T U R z))) =
      ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
        R.cocomplex).homologyπ 1) (relativeFrameAbsoluteCycle T U R z) := by
  unfold relativeFrameClass relativeFrameAbsoluteCycle
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom]
  rfl

private lemma cycles_section_exists (A : T.Etale)
    (a : (R.cocomplex.X 1).obj.obj (op A))
    (ha : (R.cocomplex.d 1 2).hom.app (op A) a = 0) :
    ∃ s : (R.cocomplex.cycles 1).obj.obj (op A),
      (R.cocomplex.iCycles 1).hom.app (op A) s = a := by
  let S := ShortComplex.mk (R.cocomplex.iCycles 1) (R.cocomplex.d 1 2)
    (R.cocomplex.iCycles_d 1 2)
  have hS : (S.map (etaleSectionFunctor A)).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ (R.cocomplex.cyclesIsKernel 1 2 (by simp))
        (etaleSectionFunctor A))
  exact ((S.map (etaleSectionFunctor A)).ab_exact_iff).1 hS a ha

private lemma relativeFrameElement_surjective
    (y : (relativeSectionComplex T U R.cocomplex).cycles 1) :
    ∃ z : ResolutionFramedLift T U R,
      relativeFrameElement T U R z =
        (relativeSectionComplex T U R.cocomplex).iCycles 1 y := by
  let C := relativeSectionComplex T U R.cocomplex
  let x := C.iCycles 1 y
  have hd : C.d 1 2 x = 0 := congrArg (fun f ↦ f y) (C.iCycles_d 1 2)
  have ha : (R.cocomplex.d 1 2).hom.app (op (Scheme.Etale.mk (𝟙 T)))
      (relativeFst T U R.cocomplex 0 x) = 0 := by
    have hh := congrArg (relativeFst T U R.cocomplex 1) hd
    erw [← ConcreteCategory.comp_apply, relative_d_fst,
      ConcreteCategory.comp_apply, map_zero] at hh
    exact hh
  obtain ⟨s, hs⟩ := cycles_section_exists T R (Scheme.Etale.mk (𝟙 T)) _ ha
  have hb : (R.cocomplex.toCycles 0 1).hom.app (op U)
      (-relativeSnd T U R.cocomplex 0 x) =
        (R.cocomplex.cycles 1).obj.map
          ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op s := by
    apply Sheaf.injective_hom_app_of_mono (R.cocomplex.iCycles 1) (op U)
    have hh := congrArg (relativeSnd T U R.cocomplex 1) hd
    erw [← ConcreteCategory.comp_apply, relative_d_snd] at hh
    simp only [AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply,
      AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply, map_zero] at hh
    have hc := eq_neg_of_add_eq_zero_left (neg_eq_zero.mp hh)
    change ((R.cocomplex.toCycles 0 1 ≫ R.cocomplex.iCycles 1).hom.app (op U))
        (-relativeSnd T U R.cocomplex 0 x) = _
    rw [R.cocomplex.toCycles_i]
    erw [map_neg, ← hc, ← hs]
    exact (congrArg (fun f ↦ f s) ((R.cocomplex.iCycles 1).hom.naturality
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op)).symm
  let z : ResolutionFramedLift T U R := ⟨s, ⟨-relativeSnd T U R.cocomplex 0 x, hb⟩⟩
  refine ⟨z, relative_coordinates_ext T U R.cocomplex 0 ?_ ?_⟩
  · exact (relativeFrameElement_coordinates T U R z).1.trans hs
  · exact (relativeFrameElement_coordinates T U R z).2.trans (neg_neg _)

/-- Every relative degree-one cohomology class has a framed lifting representative. -/
theorem relativeFrameClass_surjective : Function.Surjective (relativeFrameClass T U R) := by
  intro t
  let C := relativeSectionComplex T U R.cocomplex
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (C.homologyπ 1)).1 inferInstance t
  obtain ⟨z, hz⟩ := relativeFrameElement_surjective T U R y
  refine ⟨z, congrArg (C.homologyπ 1) ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (C.iCycles 1)).1 inferInstance
  exact (relativeFrameCycle_i T U R z).trans hz

private lemma ab_homology_eq_iff (S : ShortComplex AddCommGrpCat.{u + 1})
    (z z' : S.cycles) :
    S.homologyπ z = S.homologyπ z' ↔
      ∃ x : S.X₁, S.f x = S.iCycles z' - S.iCycles z := by
  let K := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hK : K.Exact := ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel
  constructor
  · intro h
    obtain ⟨x, hx⟩ := K.ab_exact_iff.mp hK (z' - z) (by
      change S.homologyπ (z' - z) = 0
      rw [map_sub, h, sub_self])
    refine ⟨x, ?_⟩
    have hh := congrArg S.iCycles hx
    change S.iCycles (S.toCycles x) = S.iCycles (z' - z) at hh
    simpa only [← ConcreteCategory.comp_apply, S.toCycles_i, map_sub] using hh
  · rintro ⟨x, hx⟩
    have hh : S.toCycles x = z' - z := by
      apply (AddCommGrpCat.mono_iff_injective S.iCycles).1 inferInstance
      simpa only [← ConcreteCategory.comp_apply, S.toCycles_i, map_sub] using hx
    have hz := congrArg S.homologyπ hh
    rw [← ConcreteCategory.comp_apply, S.toCycles_comp_homologyπ] at hz
    change 0 = S.homologyπ (z' - z) at hz
    rw [map_sub, eq_comm, sub_eq_zero] at hz
    exact hz.symm

private lemma complex_homology_eq_iff (C : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (y y' : C.cycles 1) :
    C.homologyπ 1 y = C.homologyπ 1 y' ↔
      ∃ x : C.X 0, C.d 0 1 x = C.iCycles 1 y' - C.iCycles 1 y := by
  let e := C.homologyIsoSc' 0 1 2 (by simp) (by simp)
  have he := (AddCommGrpCat.mono_iff_injective e.hom).1 inferInstance
  rw [← he.eq_iff]
  dsimp only [e]
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.π_homologyIsoSc'_hom]
  simp only [ConcreteCategory.comp_apply]
  rw [ab_homology_eq_iff]
  simp only [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  rfl

/-- Two framed lifts give the same relative class exactly when their pointed torsors
are isomorphic. -/
theorem relativeFrameClass_eq_iff (z z' : ResolutionFramedLift T U R) :
    relativeFrameClass T U R z = relativeFrameClass T U R z' ↔
      Sheaf.Torsor.WithSection.IsIsomorphic z.toPair z'.toPair := by
  rw [relativeFrameClass, relativeFrameClass, complex_homology_eq_iff,
    relativeFrameCycle_i, relativeFrameCycle_i, Sheaf.Torsor.FramedLift.isIsomorphic_iff]
  change (∃ y : (relativeSectionComplex T U R.cocomplex).X 0,
      (relativeSectionComplex T U R.cocomplex).d 0 1 y =
        relativeFrameElement T U R z' - relativeFrameElement T U R z) ↔
    ∃ x : (R.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk (𝟙 T))),
      (R.cocomplex.toCycles 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) x = z'.1 - z.1 ∧
      (R.cocomplex.X 0).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op x = z'.2.1 - z.2.1
  constructor
  · rintro ⟨y, hy⟩
    let x := (relativeDegreeZeroIso T U R.cocomplex).hom y
    have hx : (relativeDegreeZeroIso T U R.cocomplex).inv x = y :=
      CategoryTheory.Iso.hom_inv_id_apply _ y
    have h₁ := congrArg (relativeFst T U R.cocomplex 0) hy
    have h₂ := congrArg (relativeSnd T U R.cocomplex 0) hy
    rw [← hx] at h₁ h₂
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      relativeBoundary_fst, map_sub, (relativeFrameElement_coordinates T U R z').1,
      (relativeFrameElement_coordinates T U R z).1] at h₁
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      relativeBoundary_snd, map_sub, (relativeFrameElement_coordinates T U R z').2,
      (relativeFrameElement_coordinates T U R z).2] at h₂
    refine ⟨x, ?_, ?_⟩
    · apply Sheaf.injective_hom_app_of_mono (R.cocomplex.iCycles 1) _
      change ((R.cocomplex.toCycles 0 1 ≫ R.cocomplex.iCycles 1).hom.app
        (op (Scheme.Etale.mk (𝟙 T)))) x = _
      rw [R.cocomplex.toCycles_i, map_sub]
      exact h₁
    · change -((R.cocomplex.X 0).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op x) = _ at h₂
      have hh := congrArg Neg.neg h₂
      simpa only [neg_neg, neg_sub, neg_sub_neg] using hh
  · rintro ⟨x, h₁, h₂⟩
    refine ⟨(relativeDegreeZeroIso T U R.cocomplex).inv x,
      relative_coordinates_ext T U R.cocomplex 0 ?_ ?_⟩
    · erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        relativeBoundary_fst, map_sub, (relativeFrameElement_coordinates T U R z').1,
        (relativeFrameElement_coordinates T U R z).1]
      have hh := congrArg ((R.cocomplex.iCycles 1).hom.app
        (op (Scheme.Etale.mk (𝟙 T)))) h₁
      change ((R.cocomplex.toCycles 0 1 ≫ R.cocomplex.iCycles 1).hom.app
        (op (Scheme.Etale.mk (𝟙 T)))) x = _ at hh
      simpa only [R.cocomplex.toCycles_i, map_sub] using hh
    · erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        relativeBoundary_snd, map_sub, (relativeFrameElement_coordinates T U R z').2,
        (relativeFrameElement_coordinates T U R z).2]
      change -((R.cocomplex.X 0).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op x) = _
      rw [h₂, neg_sub]
      abel

/-- The quotient of framed lifts is the actual first homology of the relative cone. -/
noncomputable def relativeFramedLiftEquiv :
    Sheaf.Torsor.FramedLift.Classes
      (MorphismProperty.Over.mkIdTerminal @Etale T)
      (resolutionLiftSequence_shortExact T R) U ≃ relativeCohomology T U R 1 :=
  Equiv.ofBijective (Quotient.lift (relativeFrameClass T U R)
    (fun z z' h => (relativeFrameClass_eq_iff T U R z z').2 h)) (by
    constructor
    · intro x y
      induction x using Quotient.inductionOn with | _ x =>
        induction y using Quotient.inductionOn with | _ y =>
          exact fun h => Quotient.sound ((relativeFrameClass_eq_iff T U R x y).1 h)
    · intro y
      obtain ⟨z, hz⟩ := relativeFrameClass_surjective T U R y
      exact ⟨Quotient.mk _ z, hz⟩)

/-- The relative first-cohomology classification, constructed from lifting torsors. -/
noncomputable def relativeTorsorEquiv :
    Sheaf.Torsor.WithSection.Classes G U ≃ relativeCohomology T U R 1 := by
  letI : Injective (R.cocomplex.X 0) := R.injective 0
  exact (Sheaf.Torsor.FramedLift.classEquiv
    (MorphismProperty.Over.mkIdTerminal @Etale T)
    (resolutionLiftSequence_shortExact T R) U).symm.trans (relativeFramedLiftEquiv T U R)

/-- On a framed lifting torsor the equivalence takes its displayed cocycle. -/
theorem relativeTorsorEquiv_frame (z : ResolutionFramedLift T U R) :
    relativeTorsorEquiv T U R (Quotient.mk _ z.toPair) = relativeFrameClass T U R z := by
  let : Injective (R.cocomplex.X 0) := R.injective 0
  change relativeFramedLiftEquiv T U R
    ((Sheaf.Torsor.FramedLift.classEquiv
      (MorphismProperty.Over.mkIdTerminal @Etale T)
      (resolutionLiftSequence_shortExact T R) U).symm
        ((Sheaf.Torsor.FramedLift.classEquiv
          (MorphismProperty.Over.mkIdTerminal @Etale T)
          (resolutionLiftSequence_shortExact T R) U) (Quotient.mk _ z))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- A chosen equivariant lifting presentation computes the relative class. -/
theorem relativeTorsorEquiv_presentation
    (P : Sheaf.Torsor.WithSection G U)
    (s : (R.cocomplex.cycles 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (e : P.1.Iso (Sheaf.Torsor.lifts
      (MorphismProperty.Over.mkIdTerminal @Etale T)
      (resolutionLiftSequence_shortExact T R) s)) :
    relativeTorsorEquiv T U R (Quotient.mk _ P) = relativeFrameClass T U R
      ⟨s, e.iso.hom.hom.app (op U) P.2⟩ := by
  rw [← relativeTorsorEquiv_frame]
  apply congrArg (relativeTorsorEquiv T U R)
  exact Quotient.sound ⟨e, rfl⟩

/-- The ambient-resolution map supplied by a lifting presentation. -/
noncomputable def resolutionPresentationMap (P : Sheaf.Torsor G)
    (s : (R.cocomplex.cycles 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (e : P.Iso (Sheaf.Torsor.lifts
      (MorphismProperty.Over.mkIdTerminal @Etale T)
      (resolutionLiftSequence_shortExact T R) s)) :
    P.sheaf.obj ⟶ (R.cocomplex.X 0).obj ⋙ forget AddCommGrpCat.{u + 1} :=
  e.iso.hom.hom ≫ Sheaf.Torsor.liftsEmbedding
    (MorphismProperty.Over.mkIdTerminal @Etale T)
    (resolutionLiftSequence_shortExact T R) s

/-- A lifting presentation is equivariant for the augmentation. -/
theorem resolutionPresentationMap_vadd (P : Sheaf.Torsor G)
    (s : (R.cocomplex.cycles 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (e : P.Iso (Sheaf.Torsor.lifts
      (MorphismProperty.Over.mkIdTerminal @Etale T)
      (resolutionLiftSequence_shortExact T R) s))
    (A : T.Etaleᵒᵖ) (g : G.obj.obj A) (t : P.sheaf.obj.obj A) :
    (resolutionPresentationMap T R P s e).app A (P.vadd A g t) =
      (show (R.cocomplex.X 0).obj.obj A from
        (resolutionPresentationMap T R P s e).app A t) + (R.ι.f 0).hom.app A g := by
  exact congrArg Subtype.val (e.map_vadd A g t)

/-- The differential of a lifting presentation is its globally specified cocycle. -/
theorem resolutionPresentationMap_d (P : Sheaf.Torsor G)
    (s : (R.cocomplex.cycles 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (e : P.Iso (Sheaf.Torsor.lifts
      (MorphismProperty.Over.mkIdTerminal @Etale T)
      (resolutionLiftSequence_shortExact T R) s))
    (A : T.Etaleᵒᵖ) (t : P.sheaf.obj.obj A) :
    (R.cocomplex.d 0 1).hom.app A ((resolutionPresentationMap T R P s e).app A t) =
      (R.cocomplex.X 1).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from A.unop).op
        ((R.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s) := by
  have hv := Sheaf.Torsor.lifts_val
    (MorphismProperty.Over.mkIdTerminal @Etale T)
    (resolutionLiftSequence_shortExact T R) (e.iso.hom.hom.app A t)
  have hh := congrArg ((R.cocomplex.iCycles 1).hom.app A) hv
  change ((R.cocomplex.toCycles 0 1 ≫ R.cocomplex.iCycles 1).hom.app A)
    ((resolutionPresentationMap T R P s e).app A t) = _ at hh
  rw [R.cocomplex.toCycles_i] at hh
  exact hh.trans (congrArg (fun f => f s)
    ((R.cocomplex.iCycles 1).hom.naturality
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from A.unop).op))

/-- The trivial torsor with zero section represents zero. -/
theorem relativeTorsorEquiv_zero :
    relativeTorsorEquiv T U R
      (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, @id (G.obj.obj (op U)) 0⟩) = 0 := by
  let z : ResolutionFramedLift T U R := Sheaf.Torsor.FramedLift.zero
    (MorphismProperty.Over.mkIdTerminal @Etale T)
    (resolutionLiftSequence_shortExact T R) U
  have hz : Quotient.mk _ ⟨Sheaf.Torsor.trivial G, @id (G.obj.obj (op U)) 0⟩ =
      (Quotient.mk _ z.toPair : Sheaf.Torsor.WithSection.Classes G U) :=
    Quotient.sound (Sheaf.Torsor.FramedLift.zero_isIsomorphic
      (MorphismProperty.Over.mkIdTerminal @Etale T)
      (resolutionLiftSequence_shortExact T R) U)
  rw [hz, relativeTorsorEquiv_frame]
  have he : relativeFrameElement T U R z = 0 := by
    apply relative_coordinates_ext T U R.cocomplex 0
    · rw [(relativeFrameElement_coordinates T U R z).1, map_zero]
      exact map_zero _
    · rw [(relativeFrameElement_coordinates T U R z).2, map_zero]
      exact neg_zero
  have hc : relativeFrameCycle T U R z = 0 := by
    apply (AddCommGrpCat.mono_iff_injective
      ((relativeSectionComplex T U R.cocomplex).iCycles 1)).1 inferInstance
    rw [relativeFrameCycle_i, he, map_zero]
  change (relativeSectionComplex T U R.cocomplex).homologyπ 1
    (relativeFrameCycle T U R z) = 0
  rw [hc, map_zero]

section Maps

variable {T' : Scheme.{u}} (U' : T'.Etale)
  (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
  (α : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
      I) ⟶ (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T'))).mapHomologicalComplex (.up ℕ)).obj
      J))
  (β : (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I) ⟶
      (((etaleSectionFunctor U').mapHomologicalComplex (.up ℕ)).obj J))
  (h : HomologicalComplex.extendMap α ComplexShape.embeddingUpNat ≫
      relativeSectionRestriction T' U' J =
    relativeSectionRestriction T U I ≫
      HomologicalComplex.extendMap β ComplexShape.embeddingUpNat)

/-- A map of restriction cones is diagonal in the canonical biproduct coordinates. -/
lemma coneMap_XIso
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (n : ℤ) :
    (HomologicalComplex.homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f n ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod r' n (n + 1) rfl).hom =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod r n (n + 1) rfl).hom ≫
        biprod.map (a.f (n + 1)) (b.f n) := by
  apply HomologicalComplex.homotopyCofiber.ext_from_X r (n + 1) n rfl <;>
    simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom r' _ (n + 1) n rfl]

private lemma relativeMap_fst :
    (relativeFiberMap _ _
      (HomologicalComplex.extendMap α ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap β ComplexShape.embeddingUpNat) h).f 1 ≫
        relativeFst T' U' J 0 = relativeFst T U I 0 ≫ α.f 1 := by
  rw [relativeFst_eq, relativeFst_eq]
  change (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
      (fun j => ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk _ _ h)).f 0 ≫ _ = _
  dsimp only [HomologicalComplex.homotopyCofiber.fstX]
  rw [← Category.assoc, ← Category.assoc]
  erw [coneMap_XIso]
  simp only [Category.assoc]
  erw [biprod.map_fst_assoc]
  erw [HomologicalComplex.extendMap_f _ _ (rfl :
    ComplexShape.embeddingUpNat.f 1 = 1)]
  simp only [Category.assoc]
  erw [CategoryTheory.Iso.inv_hom_id, Category.comp_id]
  rfl

private lemma relativeMap_snd :
    (relativeFiberMap _ _
      (HomologicalComplex.extendMap α ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap β ComplexShape.embeddingUpNat) h).f 1 ≫
        relativeSnd T' U' J 0 = relativeSnd T U I 0 ≫ β.f 0 := by
  rw [relativeSnd_eq, relativeSnd_eq]
  change (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
      (fun j => ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk _ _ h)).f 0 ≫ _ = _
  erw [← cofiber_snd (relativeSectionRestriction T' U' J) 0 1 rfl,
    ← cofiber_snd (relativeSectionRestriction T U I) 0 1 rfl]
  rw [← Category.assoc, ← Category.assoc]
  erw [coneMap_XIso]
  simp only [Category.assoc]
  erw [biprod.map_snd_assoc]
  erw [HomologicalComplex.extendMap_f _ _ (rfl :
    ComplexShape.embeddingUpNat.f 0 = 0)]
  simp only [Category.assoc]
  erw [CategoryTheory.Iso.inv_hom_id, Category.comp_id]
  rfl

end Maps

/-- If a global section `x` witnesses the difference between `z'` and the transport of `z`,
then the induced map on relative cohomology sends the class of `z` to the class of `z'`. -/
theorem relativeFrameClass_map_eq
    {T' : Scheme.{u}} (U' : T'.Etale)
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}} (R' : InjectiveResolution G')
    (α : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
        R.cocomplex) ⟶
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T'))).mapHomologicalComplex (.up ℕ)).obj
        R'.cocomplex))
    (β : (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj R.cocomplex) ⟶
      (((etaleSectionFunctor U').mapHomologicalComplex (.up ℕ)).obj R'.cocomplex))
    (h : HomologicalComplex.extendMap α ComplexShape.embeddingUpNat ≫
        relativeSectionRestriction T' U' R'.cocomplex =
      relativeSectionRestriction T U R.cocomplex ≫
        HomologicalComplex.extendMap β ComplexShape.embeddingUpNat)
    (z : ResolutionFramedLift T U R) (z' : ResolutionFramedLift T' U' R')
    (x : (R'.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk (𝟙 T'))))
    (hd : (R'.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T'))) x =
      (R'.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T'))) z'.1 -
        (show (R'.cocomplex.X 1).obj.obj (op (Scheme.Etale.mk (𝟙 T'))) from
          α.f 1 ((R.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1)))
    (hr : (R'.cocomplex.X 0).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T').from U').op x =
      (show (R'.cocomplex.X 0).obj.obj (op U') from z'.2.1) -
        (show (R'.cocomplex.X 0).obj.obj (op U') from β.f 0 z.2.1)) :
    HomologicalComplex.homologyMap (relativeFiberMap _ _
      (HomologicalComplex.extendMap α ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap β ComplexShape.embeddingUpNat) h) 1
        (relativeFrameClass T U R z) = relativeFrameClass T' U' R' z' := by
  let φ := relativeFiberMap _ _
    (HomologicalComplex.extendMap α ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap β ComplexShape.embeddingUpNat) h
  change HomologicalComplex.homologyMap φ 1
    ((relativeSectionComplex T U R.cocomplex).homologyπ 1 (relativeFrameCycle T U R z)) = _
  erw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  apply (complex_homology_eq_iff _ _ _).2
  refine ⟨(relativeDegreeZeroIso T' U' R'.cocomplex).inv x, ?_⟩
  have hcy : (relativeSectionComplex T' U' R'.cocomplex).iCycles 1
      (HomologicalComplex.cyclesMap φ 1 (relativeFrameCycle T U R z)) =
      φ.f 1 (relativeFrameElement T U R z) := by
    erw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, relativeFrameCycle_i]
    rfl
  erw [relativeFrameCycle_i, hcy]
  apply relative_coordinates_ext T' U' R'.cocomplex 0
  · erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      relativeBoundary_fst, map_sub, (relativeFrameElement_coordinates T' U' R' z').1]
    have hm := relativeMap_fst T U R.cocomplex U' R'.cocomplex α β h
    have hh := congrArg (fun f => f (relativeFrameElement T U R z)) hm
    change _ = α.f 1 (relativeFst T U R.cocomplex 0
      (relativeFrameElement T U R z)) at hh
    rw [(relativeFrameElement_coordinates T U R z).1] at hh
    exact hd.trans (congrArg (_ - ·) hh.symm)
  · erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      relativeBoundary_snd, map_sub, (relativeFrameElement_coordinates T' U' R' z').2]
    have hm := relativeMap_snd T U R.cocomplex U' R'.cocomplex α β h
    have hh := congrArg (fun f => f (relativeFrameElement T U R z)) hm
    change _ = β.f 0 (relativeSnd T U R.cocomplex 0
      (relativeFrameElement T U R z)) at hh
    rw [(relativeFrameElement_coordinates T U R z).2, map_neg] at hh
    change -((R'.cocomplex.X 0).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T').from U').op x) = _
    change relativeSnd T' U' R'.cocomplex 0
      (φ.f 1 (relativeFrameElement T U R z)) =
      -(show (R'.cocomplex.X 0).obj.obj (op U') from β.f 0 z.2.1) at hh
    rw [hr, neg_sub, hh]
    abel

end AlgebraicGeometry.Etale

-- Check the axioms of the completed construction.
