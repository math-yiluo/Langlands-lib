/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Multiplication of complete local sections

Source: Stacks Project, Tags 0997 and 0998.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

private noncomputable def sectionTransition
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) (U : C) (f : O.obj.obj (op U)) :
    SheafOfModules.unit (O.over U) ⟶ SheafOfModules.unit (O.over U) :=
  (SheafOfModules.unit (O.over U)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V ↦ O.obj.map V.unop.hom.op f)
      (fun {V W} a ↦ ringedSiteSectionLocalization_compatible O U f V W a))

private noncomputable def sectionSequence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) (U : C) (f : O.obj.obj (op U)) :
    ℕ ⥤ SheafOfModules.{u} (O.over U) :=
  Functor.ofSequence (X := fun _ : ℕ ↦ SheafOfModules.unit (O.over U))
    (fun _ ↦ sectionTransition O U f)

private theorem sectionTransition_mul
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) (U : C) (a f : O.obj.obj (op U)) :
    sectionTransition O U (a * f) =
      sectionTransition O U a ≫ sectionTransition O U f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change O.obj.obj (op W.unop.left) at x
  change x * O.obj.map W.unop.hom.op (a * f) =
    (x * O.obj.map W.unop.hom.op a) * O.obj.map W.unop.hom.op f
  rw [map_mul, mul_assoc]

private theorem tensor_unit_endomorphisms
    {A : Type*} [Category A] [MonoidalCategory A] (s t : 𝟙_ A ⟶ 𝟙_ A) :
    (s ⊗ₘ t) ≫ (λ_ (𝟙_ A)).hom = (λ_ (𝟙_ A)).hom ≫ s ≫ t := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality]
  rw [← Category.assoc, unitors_equal, rightUnitor_naturality, ← unitors_equal,
    Category.assoc]

private theorem tensor_monoidalPreadditive
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] : MonoidalPreadditive A := by
  have (M : A) : (tensorLeft M).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := inferInstance
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

private theorem localization_tensor_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (a f : R.obj.obj (op U)) :
    let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
    letI : MonoidalCategory (SheafOfModules.{u} (O.over U)) :=
      SheafOfModules.monoidalCategory (R.over U)
    Nonempty (ringedSiteSectionLocalization O U a ⊗ ringedSiteSectionLocalization O U f ≅
      ringedSiteSectionLocalization O U (a * f)) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let A := SheafOfModules.{u} (O.over U)
  let : MonoidalCategory A := SheafOfModules.monoidalCategory (R.over U)
  let : SymmetricCategory A := SheafOfModules.symmetricCategory (R.over U)
  let : MonoidalClosed A := SheafOfModules.monoidalClosed (R := R.over U)
  let M := SheafOfModules.unit (O.over U)
  let Da := sectionSequence O U a
  let Df := sectionSequence O U f
  let Daf := sectionSequence O U (a * f)
  have h (n : ℕ) :
      (Da ⊗ Df).map (homOfLE (Nat.le_add_right n 1)) ≫ (λ_ M).hom =
        (λ_ M).hom ≫ Daf.map (homOfLE (Nat.le_add_right n 1)) := by
    simp only [Monoidal.tensorObj_map, Da, Df, Daf, sectionSequence,
      Functor.ofSequence_map_homOfLE_succ]
    change (sectionTransition O U a ⊗ₘ sectionTransition O U f) ≫ (λ_ M).hom =
      (λ_ M).hom ≫ sectionTransition O U (a * f)
    rw [sectionTransition_mul]
    exact tensor_unit_endomorphisms _ _
  let α : Da ⊗ Df ⟶ Daf := NatTrans.ofSequence (fun _ ↦ (λ_ M).hom) h
  let e : Da ⊗ Df ≅ Daf := NatIso.ofComponents (fun _ ↦ λ_ M)
    (fun b ↦ α.naturality b)
  let hc := (colimit.isColimit Da).tensor (colimit.isColimit Df)
  exact ⟨hc.coconePointUniqueUpToIso (colimit.isColimit (Da ⊗ Df)) ≪≫
    HasColimit.isoOfNatIso e⟩

private theorem localization_flat
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U)) :
    SheafOfModules.IsFlat (R := R.over U)
      (ringedSiteSectionLocalization
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U f) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let A := SheafOfModules.{u} (O.over U)
  let : MonoidalCategory A := SheafOfModules.monoidalCategory (R.over U)
  let : SymmetricCategory A := SheafOfModules.symmetricCategory (R.over U)
  let : MonoidalClosed A := SheafOfModules.monoidalClosed (R := R.over U)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  have : AB5OfSize.{0, 0} A := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℕ A := AB5OfSize.ofShape ℕ
  let D := sectionSequence O U f
  have (n : ℕ) : PreservesFiniteLimits (tensorLeft (D.obj n)) := by
    change PreservesFiniteLimits (tensorLeft (𝟙_ A))
    exact preservesFiniteLimits_of_natIso (leftUnitorNatIso A).symm
  have : PreservesColimit D (curriedTensor A) :=
    MonoidalCategory.Limits.preservesColimit_curriedTensor _
  let e : tensorLeft (colimit D) ≅ (D ⋙ curriedTensor A).flip ⋙ colim :=
    preservesColimitIso (curriedTensor A) D ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((D ⋙ curriedTensor A).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun n ↦
      inferInstanceAs (PreservesFiniteLimits (tensorLeft (D.obj n))))
  have : PreservesFiniteLimits (tensorLeft (colimit D)) :=
    preservesFiniteLimits_of_natIso e.symm
  exact ((ObjectProperty.flat_iff_preservesFiniteLimits (colimit D)).mpr inferInstance).tensorRight

/-- For a complete section f and any a, completeness is preserved by multiplication by a.

Proof: Work on the slice over U. Localization at af is the tensor product of the
localizations at a and f. These localization modules are flat, so the ordinary tensor
is the derived tensor. Tensor-Hom currying identifies RHom(O[1/(af)],K) with
RHom(O[1/a],RHom(O[1/f],K)). The inner derived object is zero by the hypothesis,
and internal Hom into zero is zero. The tensor formula follows directly from
preservation of sequential colimits
by tensor and the cofinal diagonal ℕ→ℕ×ℕ; the transition map is multiplication
by af. Exact filtered colimits show that these colimits of the flat unit module
are flat. No cancellation
or nonzero assumption is used; a=0 and f=0 give the zero localization.

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998;
sites-cohomology.tex, Tag 08JB.
(auxiliary; not a blueprint node). -/
theorem ringedSite_completeElement_mul
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U : C) (a f : R.obj.obj (op U))
    (hf : IsRingedSiteCompleteElement J R K U f) :
    IsRingedSiteCompleteElement J R K U (a * f) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let A := SheafOfModules.{u} (O.over U)
  let : ∀ W : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (R.over W))) :=
    fun W ↦ inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (O.over W)))
  let : MonoidalCategory A := SheafOfModules.monoidalCategory (R.over U)
  let : SymmetricCategory A := SheafOfModules.symmetricCategory (R.over U)
  let : MonoidalClosed A := SheafOfModules.monoidalClosed (R := R.over U)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let : MonoidalPreadditive A := tensor_monoidalPreadditive
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let N := ringedSiteDerivedRestriction O U K
  let : Category.{w} (@DerivedCategory (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) _ _
      (inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (O.over U))))) :=
    inferInstanceAs (Category.{w} (DerivedCategory (SheafOfModules.{u} (O.over U))))
  let P := Q.objPreimage N
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj P
  let η := (CochainComplex.toKInjectiveResolution.{u} A).app P
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A P).2
  have : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A P
  have : IsIso (Q.map η) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ η).mpr inferInstance
  let eI : Q.obj I ≅ N := (asIso (Q.map η)).symm ≪≫ Q.objObjPreimageIso N
  let single := HomologicalComplex.single A (.up ℤ) 0
  let La := single.obj (ringedSiteSectionLocalization O U a)
  let Lf := single.obj (ringedSiteSectionLocalization O U f)
  let Laf := single.obj (ringedSiteSectionLocalization O U (a * f))
  let Hf := homComplex (R := R.over U) Lf I
  obtain ⟨eF⟩ := derivedInternalHom_obj_iso (J.over U) (R.over U)
    (Q.obj Lf) N Lf I (Iso.refl _) eI
  have hHf : IsZero (Q.obj Hf) := hf.of_iso eF.symm
  have hflat : CochainComplex.IsKFlatTensor (R := R.over U) Lf := by
    apply CochainComplex.isKFlat_of_boundedAbove_flat (R := R.over U)
    · exact ⟨0, fun n hn ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ (ne_of_gt hn)⟩
    · intro n
      by_cases hn : n = 0
      · subst n
        exact (exactFunctor _ _).prop_of_iso
          ((curriedTensor A).flip.mapIso
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (ringedSiteSectionLocalization O U f)).symm)
          (localization_flat R U f)
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
          (ringedSiteSectionLocalization O U f) n hn
        exact (ObjectProperty.flat_of_isZero hz).tensorRight
  have : Hf.IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlat (R := R.over U) Lf I hflat
  obtain ⟨shift, htri⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).1 (Q.obj La)
  let := shift
  have := htri
  have hz := ((Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).obj
    (op (Q.obj La))).map_isZero hHf
  obtain ⟨eOuter⟩ := derivedInternalHom_obj_iso (J.over U) (R.over U)
    (Q.obj La) (Q.obj Hf) La Hf (Iso.refl _) (Iso.refl _)
  have hOuter := hz.of_iso eOuter.symm
  obtain ⟨curry, _⟩ := homComplex_tensorTotal_iso (R.over U)
  have hTotal := hOuter.of_iso (Q.mapIso (curry La Lf I)).symm
  obtain ⟨eTensor⟩ := localization_tensor_iso R U a f
  let eComplex : CochainComplex.mapBifunctor La Lf (curriedTensor A) ≅ Laf :=
    CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A)
      (ringedSiteSectionLocalization O U a) Lf ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      (tensorLeft (ringedSiteSectionLocalization O U a)) (.up ℤ) 0).app
        (ringedSiteSectionLocalization O U f) ≪≫ single.mapIso eTensor
  let eHom := ((homComplexFunctor (R := R.over U)).mapIso eComplex.op.symm).app I
  have hFinal := hTotal.of_iso (Q.mapIso eHom).symm
  obtain ⟨eFinal⟩ := derivedInternalHom_obj_iso (J.over U) (R.over U)
    (Q.obj Laf) N Laf I (Iso.refl _) eI
  exact hFinal.of_iso eFinal

end CategoryTheory
