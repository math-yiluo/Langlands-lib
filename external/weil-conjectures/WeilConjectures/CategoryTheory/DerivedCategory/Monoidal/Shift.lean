/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated

/-!
# The derived tensor product commutes with shifts

Let `C` be an abelian monoidal category whose derived category `D(C)` carries the derived
tensor product `- ⊗ᴸ -` obtained from the K-flat left derivability structure (see
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`). This file shows that the
derived tensor product commutes with the shifts by `ℤ` in both variables, as a bifunctor
(`Functor.CommShift₂Int`): the commutation isomorphisms of `K ⊗ᴸ -` and `- ⊗ᴸ K` are natural in
`K` and the two ways to identify `X⟦a⟧ ⊗ᴸ Y⟦b⟧` with `(X ⊗ᴸ Y)⟦a + b⟧` differ by the sign
`(-1) ^ (a * b)`. Both `K ⊗ᴸ -` and `- ⊗ᴸ K` are triangulated functors.

## Construction

For a K-flat complex `P`, the comparison `Qh.obj P ⊗ᴸ Qh.obj Z ⟶ Qh.obj (P ⊗ Z)` is an
isomorphism for every `Z` (`DerivedMonoidal.isIso_counit_app_app_of_kFlat_left`). Over a
monoidal closed braided Grothendieck abelian category with functorial flat resolutions, the
K-flat cochain complexes have functorial resolutions, so their inclusion induces an equivalence
of localizations (`DerivedCategory.isLocalizedEquivalence_localizerMorphismKFlat`). Hence the
derived tensor product is induced, through the localization functors from K-flat cochain
complexes and from all cochain complexes, by the bifunctor `(P, Z) ↦ Qh (P ⊗ Z)`, which
commutes with shifts in both variables by Mathlib's `Functor.map₂CochainComplex` instance. The
two-variable structure is then `Functor.commShift₂OfLocalization`.

On `Qh.obj P` for `P` K-flat, the one-variable structures agree with those induced through `Qh`
by `P ⊗ -` and `- ⊗ P` (`DerivedCategory.commShiftTensorLeft_eq`,
`DerivedCategory.commShiftTensorRight_eq`), which are triangulated; triangulatedness is
transported to every object along an isomorphism `Qh.obj P ≅ K`, using the naturality of the
structure.

## Main definitions

- `DerivedCategory.commShift₂CurriedTensor` : the instance
  `(curriedTensor (DerivedCategory C)).CommShift₂Int`.
- `DerivedCategory.commShiftTensorLeft`, `DerivedCategory.commShiftTensorRight` : the induced
  instances on `K ⊗ᴸ -` and `- ⊗ᴸ K`.
- `DerivedCategory.shiftTensorShiftIso` : the isomorphism `X⟦a⟧ ⊗ᴸ Y⟦b⟧ ≅ (X ⊗ᴸ Y)⟦a + b⟧`.

## Main results

- `DerivedCategory.isTriangulated_tensorLeft`, `DerivedCategory.isTriangulated_tensorRight` :
  `K ⊗ᴸ -` and `- ⊗ᴸ K` are triangulated functors.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u s

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]

/-- Every object of the derived category is isomorphic to the image of a K-flat complex. -/
lemma exists_kFlat_iso (K : DerivedCategory C) :
    ∃ (P : HomotopyCategory C (ComplexShape.up ℤ)),
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P ∧
        Nonempty (Qh.obj P ≅ K) := by
  have R : (HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.LeftResolution (Qh.objPreimage K) :=
    Classical.arbitrary _
  have := Localization.inverts Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso K⟩⟩

variable (P : HomotopyCategory C (ComplexShape.up ℤ))

/-- The comparison `Qh.obj P ⊗ᴸ Qh.obj Z ⟶ Qh.obj (P ⊗ Z)`, natural in `Z`. -/
noncomputable def tensorLeftCounit :
    Qh ⋙ (curriedTensor _).obj (Qh.obj P) ⟶ (curriedTensor _).obj P ⋙ Qh :=
  Functor.bifunctorCounit₁ (Functor.LaxMonoidal.μNatTrans Qh) P

/-- The comparison `Qh.obj Z ⊗ᴸ Qh.obj P ⟶ Qh.obj (Z ⊗ P)`, natural in `Z`. -/
noncomputable def tensorRightCounit :
    Qh ⋙ (curriedTensor _).flip.obj (Qh.obj P) ⟶ (curriedTensor _).flip.obj P ⋙ Qh :=
  Functor.bifunctorCounit₂ (Functor.LaxMonoidal.μNatTrans Qh) P

/-- If `P` is K-flat, the comparison `Qh.obj P ⊗ᴸ Qh.obj Z ⟶ Qh.obj (P ⊗ Z)` is an
isomorphism for every `Z`. -/
lemma isIso_tensorLeftCounit (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    IsIso (tensorLeftCounit P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh _ P Z hP

/-- If `P` is K-flat, the comparison `Qh.obj Z ⊗ᴸ Qh.obj P ⟶ Qh.obj (Z ⊗ P)` is an
isomorphism for every `Z`. -/
lemma isIso_tensorRightCounit (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    IsIso (tensorRightCounit P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_right Qh _ Z P hP

/-- For a K-flat complex `P`, the functor `Qh.obj P ⊗ᴸ -` commutes with the shift, being
induced through the localization `Qh` by the functor `(P ⊗ -) ⋙ Qh`, which does. -/
@[instance_reducible]
noncomputable def commShiftTensorLeftQhObj
    (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    ((curriedTensor (DerivedCategory C)).obj (Qh.obj P)).CommShift ℤ :=
  have := isIso_tensorLeftCounit P hP
  letI : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).obj P ⋙ Qh) ((curriedTensor _).obj (Qh.obj P)) :=
    ⟨asIso (tensorLeftCounit P)⟩
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((curriedTensor _).obj P ⋙ Qh) _

/-- For a K-flat complex `P`, the functor `- ⊗ᴸ Qh.obj P` commutes with the shift, being
induced through the localization `Qh` by the functor `(- ⊗ P) ⋙ Qh`, which does. -/
@[instance_reducible]
noncomputable def commShiftTensorRightQhObj
    (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    ((curriedTensor (DerivedCategory C)).flip.obj (Qh.obj P)).CommShift ℤ :=
  have := isIso_tensorRightCounit P hP
  letI : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj P ⋙ Qh) ((curriedTensor _).flip.obj (Qh.obj P)) :=
    ⟨asIso (tensorRightCounit P)⟩
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((curriedTensor _).flip.obj P ⋙ Qh) _

/-- For a K-flat complex `P`, the functor `- ⊗ᴸ Qh.obj P` is triangulated: it is induced
through the triangulated localization `Qh` by the triangulated functor `(- ⊗ P) ⋙ Qh`. -/
lemma isTriangulated_tensorRightQhObj
    (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    letI := commShiftTensorRightQhObj P hP
    ((curriedTensor (DerivedCategory C)).flip.obj (Qh.obj P)).IsTriangulated := by
  let := commShiftTensorRightQhObj P hP
  have := isIso_tensorRightCounit P hP
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj P ⋙ Qh) ((curriedTensor _).flip.obj (Qh.obj P)) :=
    ⟨asIso (tensorRightCounit P)⟩
  have := Localization.essSurj_mapArrow Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj P ⋙ Qh) ((curriedTensor _).flip.obj (Qh.obj P)))

/-- For a K-flat complex `P`, the functor `Qh.obj P ⊗ᴸ -` is triangulated: it is induced
through the triangulated localization `Qh` by the triangulated functor `(P ⊗ -) ⋙ Qh`. -/
lemma isTriangulated_tensorLeftQhObj
    (hP : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat P) :
    letI := commShiftTensorLeftQhObj P hP
    ((curriedTensor (DerivedCategory C)).obj (Qh.obj P)).IsTriangulated := by
  let := commShiftTensorLeftQhObj P hP
  have := isIso_tensorLeftCounit P hP
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).obj P ⋙ Qh) ((curriedTensor _).obj (Qh.obj P)) :=
    ⟨asIso (tensorLeftCounit P)⟩
  have := Localization.essSurj_mapArrow Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).obj P ⋙ Qh) ((curriedTensor _).obj (Qh.obj P)))

end DerivedCategory

namespace DerivedCategory

section GrothendieckAbelian

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance localInstance_Shift_1 : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

/-- The inclusion of K-flat cochain complexes induces an equivalence of the localizations with
respect to quasi-isomorphisms: every complex has a functorial K-flat resolution. -/
instance isLocalizedEquivalence_localizerMorphismKFlat :
    (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat.IsLocalizedEquivalence := by
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  exact LocalizerMorphism.isLocalizedEquivalence_of_functorial_left_resolutions _
    (Λ.reduced.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le)
    (fun _ ↦ by rw [HomologicalComplex.mem_quasiIso_iff]; dsimp; infer_instance) rfl

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

namespace TensorCommShift₂

/-- The localization functor `K(C) ⥤ D(C)` precomposed with the quotient
`CochainComplex C ℤ ⥤ K(C)`. -/
noncomputable abbrev L : CochainComplex C ℤ ⥤ DerivedCategory C :=
  HomotopyCategory.quotient C (.up ℤ) ⋙ Qh

instance : (L C).IsLocalization (HomologicalComplex.quasiIso C (.up ℤ)) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C).symm

/-- The localization functor restricted to K-flat cochain complexes. -/
noncomputable abbrev LKFlat : CochainComplex.KFlat C ⥤ DerivedCategory C :=
  CochainComplex.ιKFlat C ⋙ L C

instance : (LKFlat C).IsLocalization (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat :=
  inferInstanceAs (((HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat.functor ⋙
    L C).IsLocalization _)

noncomputable instance : (curriedTensor (CochainComplex C ℤ)).CommShift₂Int :=
  inferInstanceAs ((curriedTensor C).map₂CochainComplex.CommShift₂Int)

/-- The tensor product of a K-flat complex with a complex, followed by the localization functor:
the bifunctor which is localized to the derived tensor product. -/
noncomputable abbrev F : CochainComplex.KFlat C ⥤ CochainComplex C ℤ ⥤ DerivedCategory C :=
  (CochainComplex.ιKFlat C ⋙ curriedTensor (CochainComplex C ℤ)) ⋙
    (Functor.whiskeringRight _ _ _).obj (L C)

noncomputable instance : (F C).CommShift₂Int := Functor.CommShift₂.postcompInt _ _

/-- The comparison `Qh P ⊗ᴸ Qh K ⟶ Qh (P ⊗ K)` for a K-flat complex `P` and a complex `K`. -/
noncomputable def liftingIsoHom :
    (((Functor.whiskeringLeft₂ _).obj (LKFlat C)).obj (L C)).obj
      (curriedTensor (DerivedCategory C)) ⟶ F C :=
  (((Functor.whiskeringLeft₂ (DerivedCategory C)).obj
    (CochainComplex.ιKFlat C ⋙ HomotopyCategory.quotient C _)).obj
      (HomotopyCategory.quotient C _)).map (Functor.LaxMonoidal.μNatTrans Qh)

instance : IsIso (liftingIsoHom C) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh _ _ _
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2)

noncomputable instance lifting :
    Localization.Lifting₂ (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (HomologicalComplex.quasiIso C (.up ℤ)) (F C) (curriedTensor (DerivedCategory C)) where
  iso := asIso (liftingIsoHom C)

end TensorCommShift₂

open TensorCommShift₂ in
/-- The derived tensor product commutes with the shifts by `ℤ` in both variables, with the
sign `(-1) ^ (p * q)` when shifting the first variable by `p` and the second by `q`. It is
induced through the localization functors by the commutation with shifts of the tensor
product of cochain complexes (`Functor.commShift₂OfLocalization`). -/
noncomputable instance commShift₂CurriedTensor :
    (curriedTensor (DerivedCategory C)).CommShift₂Int :=
  Functor.commShift₂OfLocalization (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (HomologicalComplex.quasiIso C (.up ℤ)) (F C) _ .int

/-- The derived tensor product `K ⊗ᴸ -` commutes with the shift by `ℤ`, by
`DerivedCategory.commShift₂CurriedTensor`. -/
noncomputable instance commShiftTensorLeft (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ :=
  Functor.CommShift₂.commShiftObj (h := .int) K

/-- The derived tensor product `- ⊗ᴸ K` commutes with the shift by `ℤ`, by
`DerivedCategory.commShift₂CurriedTensor`. -/
noncomputable instance commShiftTensorRight (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ :=
  Functor.CommShift₂.commShiftFlipObj (h := .int) K

open TensorCommShift₂ in
/-- On `Qh.obj P` for a K-flat complex `P`, the commutation of `K ⊗ᴸ -` with the shifts given
by `DerivedCategory.commShift₂CurriedTensor` is the one of `commShiftTensorLeftQhObj`, which is
induced through `Qh` by `P ⊗ -`. -/
lemma commShiftTensorLeft_eq (P : CochainComplex.KFlat C) :
    commShiftTensorLeft C ((LKFlat C).obj P) =
      commShiftTensorLeftQhObj ((HomotopyCategory.quotient C _).obj P.obj)
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2) := by
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2
  refine Functor.CommShift.eq_of_natTransCommShift (L C) (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ ((Localization.Lifting₂.iso (LKFlat C) (L C) _ _ (F C)
      (curriedTensor (DerivedCategory C))).app P)
    (Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (LKFlat C) (L C) _ _ (F C) _ P) ?_
  let := commShiftTensorLeftQhObj ((HomotopyCategory.quotient C _).obj P.obj) hP
  have := isIso_tensorLeftCounit ((HomotopyCategory.quotient C _).obj P.obj) hP
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).obj ((HomotopyCategory.quotient C _).obj P.obj) ⋙ Qh)
      ((curriedTensor _).obj (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj))) :=
    ⟨asIso (tensorLeftCounit _)⟩
  have h := NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.quasiIso C (.up ℤ)) ℤ
    ((curriedTensor _).obj ((HomotopyCategory.quotient C _).obj P.obj) ⋙ Qh)
    ((curriedTensor (DerivedCategory C)).obj
      (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj)))
  have : NatTrans.CommShift (tensorLeftCounit ((HomotopyCategory.quotient C _).obj P.obj)) ℤ :=
    h
  change NatTrans.CommShift (F₁ := L C ⋙ (curriedTensor _).obj
    (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj)))
    (Functor.CommShift₂OfLocalization.liftingIsoApp (LKFlat C) (L C)
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ)) (F C)
    (curriedTensor (DerivedCategory C)) P) ℤ
  have eq : (Functor.CommShift₂OfLocalization.liftingIsoApp (LKFlat C) (L C)
      (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ)) (F C)
      (curriedTensor (DerivedCategory C)) P : L C ⋙ (curriedTensor _).obj
        (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj)) ⟶ _) =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient C _)
          (tensorLeftCounit ((HomotopyCategory.quotient C _).obj P.obj)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((curriedTensor C).quotientCompBifunctorMapHomotopyObjIso
          (.up ℤ) (.up ℤ) (.up ℤ) P.obj).hom Qh ≫
        (Functor.associator _ _ _).hom := by
    rw [show ((curriedTensor C).quotientCompBifunctorMapHomotopyObjIso
      (.up ℤ) (.up ℤ) (.up ℤ) P.obj).hom = 𝟙 _ from rfl, Functor.whiskerRight_id']
    ext K
    dsimp
    simp only [Category.id_comp, Category.comp_id]
    exact (Category.comp_id ((tensorLeftCounit ((HomotopyCategory.quotient C _).obj P.obj)).app
      ((HomotopyCategory.quotient C _).obj K))).symm
  rw [eq]
  infer_instance

open TensorCommShift₂ in
/-- On `Qh.obj P` for a K-flat complex `P`, the commutation of `- ⊗ᴸ K` with the shifts given
by `DerivedCategory.commShift₂CurriedTensor` is the one of `commShiftTensorRightQhObj`, which is
induced through `Qh` by `- ⊗ P`. -/
lemma commShiftTensorRight_eq (P : CochainComplex.KFlat C) :
    commShiftTensorRight C ((LKFlat C).obj P) =
      commShiftTensorRightQhObj ((HomotopyCategory.quotient C _).obj P.obj)
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2) := by
  -- Reuse the coproduct and graded-tensor instances throughout the localization comparison.
  have (J : Type) : HasColimitsOfShape (Discrete J) C := inferInstance
  have (X₁ X₂ : GradedObject ℤ C) : X₁.HasTensor X₂ := inferInstance
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ C) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2
  refine Functor.CommShift.eq_of_natTransCommShift (LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat _ _
    ((Localization.Lifting₂.iso (L C) (LKFlat C) _ _ (F C).flip
      (curriedTensor (DerivedCategory C)).flip).app P.obj)
    (Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (L C) (LKFlat C) _ _ (F C).flip _
      P.obj) ?_
  let := commShiftTensorRightQhObj ((HomotopyCategory.quotient C _).obj P.obj) hP
  have := isIso_tensorRightCounit ((HomotopyCategory.quotient C _).obj P.obj) hP
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj P.obj) ⋙ Qh)
      ((curriedTensor _).flip.obj (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj))) :=
    ⟨asIso (tensorRightCounit _)⟩
  have h := NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.quasiIso C (.up ℤ)) ℤ
    ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj P.obj) ⋙ Qh)
    ((curriedTensor (DerivedCategory C)).flip.obj
      (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj)))
  have : NatTrans.CommShift (tensorRightCounit ((HomotopyCategory.quotient C _).obj P.obj)) ℤ :=
    h
  change NatTrans.CommShift (F₁ := LKFlat C ⋙ (curriedTensor _).flip.obj
    (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj)))
    (Functor.CommShift₂OfLocalization.liftingIsoApp (L C) (LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip P.obj) ℤ
  have eq : (Functor.CommShift₂OfLocalization.liftingIsoApp (L C) (LKFlat C)
      (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (F C).flip (curriedTensor (DerivedCategory C)).flip P.obj : LKFlat C ⋙
        (curriedTensor _).flip.obj (Qh.obj ((HomotopyCategory.quotient C _).obj P.obj)) ⟶ _) =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (CochainComplex.ιKFlat C) ((Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (HomotopyCategory.quotient C _)
            (tensorRightCounit ((HomotopyCategory.quotient C _).obj P.obj)) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight ((curriedTensor C).quotientCompBifunctorMapHomotopyFlipObjIso
            (.up ℤ) (.up ℤ) (.up ℤ) P.obj).hom Qh ≫
          (Functor.associator _ _ _).hom) ≫
        (Functor.associator _ _ _).inv := by
    rw [show ((curriedTensor C).quotientCompBifunctorMapHomotopyFlipObjIso
      (.up ℤ) (.up ℤ) (.up ℤ) P.obj).hom = 𝟙 _ from rfl, Functor.whiskerRight_id']
    ext K
    dsimp
    simp only [Category.id_comp, Category.comp_id]
    exact (Category.comp_id ((tensorRightCounit ((HomotopyCategory.quotient C _).obj P.obj)).app
      ((HomotopyCategory.quotient C _).obj K.obj))).symm
  rw [eq]
  infer_instance

open TensorCommShift₂ in
/-- The derived tensor product `K ⊗ᴸ -` is a triangulated functor, for the commutation with
shifts `DerivedCategory.commShiftTensorLeft`. -/
instance isTriangulated_tensorLeft (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).obj K).IsTriangulated := by
  have := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  let P := (LKFlat C).objPreimage K
  have hP : ((curriedTensor (DerivedCategory C)).obj ((LKFlat C).obj P)).IsTriangulated := by
    have h := isTriangulated_tensorLeftQhObj ((HomotopyCategory.quotient C _).obj P.obj)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2)
    rw [← commShiftTensorLeft_eq] at h
    exact h
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory C)).mapIso
      ((LKFlat C).objObjPreimageIso K)).hom ℤ :=
    Functor.CommShift₂.commShift_map (G := curriedTensor (DerivedCategory C)) (h := .int) _
  exact Functor.isTriangulated_of_iso
    ((curriedTensor (DerivedCategory C)).mapIso ((LKFlat C).objObjPreimageIso K))

open TensorCommShift₂ in
/-- The derived tensor product `- ⊗ᴸ K` is a triangulated functor, for the commutation with
shifts `DerivedCategory.commShiftTensorRight`. -/
instance isTriangulated_tensorRight (K : DerivedCategory C) :
    ((curriedTensor (DerivedCategory C)).flip.obj K).IsTriangulated := by
  have := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  let P := (LKFlat C).objPreimage K
  have hP : ((curriedTensor (DerivedCategory C)).flip.obj ((LKFlat C).obj P)).IsTriangulated := by
    have h := isTriangulated_tensorRightQhObj ((HomotopyCategory.quotient C _).obj P.obj)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2)
    rw [← commShiftTensorRight_eq] at h
    exact h
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory C)).flip.mapIso
      ((LKFlat C).objObjPreimageIso K)).hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (G := curriedTensor (DerivedCategory C)) (h := .int) _
  exact Functor.isTriangulated_of_iso
    ((curriedTensor (DerivedCategory C)).flip.mapIso ((LKFlat C).objObjPreimageIso K))

/-- The derived tensor product, as `X⟦a⟧ ⊗ᴸ Y⟦b⟧ ≅ (X ⊗ᴸ Y)⟦a + b⟧`. -/
noncomputable def shiftTensorShiftIso (X Y : DerivedCategory C) (a b : ℤ) :
    X⟦a⟧ ⊗ Y⟦b⟧ ≅ (X ⊗ Y)⟦a + b⟧ :=
  (((curriedTensor (DerivedCategory C)).flip.obj (Y⟦b⟧)).commShiftIso a).app X ≪≫
    (shiftFunctor _ a).mapIso ((((curriedTensor _).obj X).commShiftIso b).app Y) ≪≫
    (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).symm.app _

end GrothendieckAbelian

end DerivedCategory
