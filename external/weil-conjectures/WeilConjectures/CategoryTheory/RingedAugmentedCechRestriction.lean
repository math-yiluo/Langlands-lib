/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Restriction of the augmented extended Cech complex

Source: Stacks Project, sites-cohomology.tex, Tag 08JB.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section RestrictionCalculation

private def tensorArrowRestriction
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (R : A ⥤ B)
    (e : T ⋙ R ≅ (R.prod R) ⋙ T')
    {X Y Z W : A} {X' Y' Z' W' : B}
    {a : X ⟶ Y} {b : Z ⟶ W} {a' : X' ⟶ Y'} {b' : Z' ⟶ W'}
    (ha : Arrow.mk (R.map a) ≅ Arrow.mk a')
    (hb : Arrow.mk (R.map b) ≅ Arrow.mk b') :
    Arrow.mk (R.map (T.map (Prod.mkHom a b))) ≅ Arrow.mk (T'.map (Prod.mkHom a' b')) := by
  let l := e.app (X, Z) ≪≫
    T'.mapIso ((Arrow.leftFunc.mapIso ha).prod (Arrow.leftFunc.mapIso hb))
  let r := e.app (Y, W) ≪≫
    T'.mapIso ((Arrow.rightFunc.mapIso ha).prod (Arrow.rightFunc.mapIso hb))
  have he : R.map (T.map (Prod.mkHom a b)) ≫ e.hom.app (Y, W) =
      e.hom.app (X, Z) ≫ T'.map (Prod.mkHom (R.map a) (R.map b)) :=
    e.hom.naturality (Prod.mkHom a b)
  refine Arrow.isoMk l r ?_
  simp only [l, r, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Arrow.mk_hom, Arrow.leftFunc_map, Arrow.rightFunc_map]
  rw [Category.assoc, ← T'.map_comp, ← Category.assoc, he]
  simp only [Category.assoc, ← T'.map_comp]
  congr 2
  ext
  · exact ha.hom.w
  · exact hb.hom.w

private def actualTensor {E : Type u} [SmallCategory E]
    {L : GrothendieckTopology E} (P : Sheaf L CommRingCat.{u}) :
    ringedSiteComplex P × ringedSiteComplex P ⥤ ringedSiteComplex P :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj P)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory P
  letI := SheafOfModules.symmetricCategory P
  letI := (SheafOfModules.tensorClosed P).1.some
  letI := (SheafOfModules.tensorClosed P).2.1.some
  MonoidalCategory.tensor (ringedSiteComplex P)

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
  (O : Sheaf K CommRingCat.{u})

private instance restriction_additive :
    (SheafOfModules.sliceCommModuleRestriction (J := J) F O).Additive := by
  constructor
  intro M N f g
  ext W x
  rfl

private theorem restriction_colimits :
    PreservesColimitsOfSize.{0, 0} (SheafOfModules.sliceCommModuleRestriction (J := J) F O) := by
  let R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj O
  let S := (F.sheafPushforwardContinuous RingCat J K).obj R
  let H := F.sheafPushforwardContinuous AddCommGrpCat.{u} J K
  have : PreservesColimitsOfSize.{u, u} H :=
    (F.sheafAdjunctionCocontinuous AddCommGrpCat.{u} J K).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} H :=
    preservesSmallestColimits_of_preservesColimits H
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{u} R) :=
    { preservesColimitsOfShape := inferInstance }
  let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
  let T := SheafOfModules.toSheaf.{u} S
  have : PreservesColimitsOfSize.{0, 0} (V ⋙ T) := by
    change PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{u} R ⋙ H)
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} T :=
    { preservesColimitsOfShape := inferInstance }
  have : ReflectsColimitsOfSize.{0, 0} T :=
    reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves V T

private def restrictionTensorNatIso :
    let := SheafOfModules.monoidalCategory O
    let P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
    let := SheafOfModules.monoidalCategory P
    let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
    (Functor.postcompose₂.obj V).obj (MonoidalCategory.curriedTensor _) ≅
      (((Functor.whiskeringLeft₂ _).obj V).obj V).obj
        (MonoidalCategory.curriedTensor _) := by
  dsimp only
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun N ↦ SheafOfModules.sliceTensorIso (J := J) F O M N) ?_) ?_
  · intro N N' g
    simpa using SheafOfModules.sliceTensorIso_natural (J := J) F O (𝟙 M) g
  · intro M M' f
    apply NatTrans.ext
    funext N
    simpa using SheafOfModules.sliceTensorIso_natural (J := J) F O f (𝟙 N)

private def restrictionTensorComplexNatIso :
    let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
    let Vc := V.mapHomologicalComplex (.up ℤ)
    let P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
    actualTensor O ⋙ Vc ≅
      (Vc.prod Vc) ⋙ actualTensor P := by
  let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
  let P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.monoidalCategory P
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed P).1.some
  have := restriction_colimits (J := J) F O
  refine NatIso.ofComponents (fun p ↦ asIso (HomologicalComplex.mapBifunctorComparison
    (restrictionTensorNatIso (J := J) F O).hom (.up ℤ) p.1 p.2)) ?_
  intro p q f
  simp only [asIso_hom]
  exact HomologicalComplex.mapBifunctorComparison_naturality
    (restrictionTensorNatIso (J := J) F O).hom (.up ℤ) f.1 f.2

private def restrictionRingComplexIso :
    let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
    let P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
    (V.mapHomologicalComplex (.up ℤ)).obj (ringedSiteRingComplex O) ≅
      ringedSiteRingComplex P := by
  let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
  exact (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).app _

private theorem augmentedCechRestriction_of_factors
    (hfactor : ∀ s : (O.obj ⋙ forget CommRingCat).sections,
      let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
      let P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
      Nonempty (Arrow.mk ((V.mapHomologicalComplex (.up ℤ)).map
          (ringedLocalizationTwoTermAugmentation O s)) ≅
        Arrow.mk (ringedLocalizationTwoTermAugmentation P
          (LocalizationRHom.restrictedSection (K := J) F O s))))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
    let P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
    Nonempty (Arrow.mk ((V.mapHomologicalComplex (.up ℤ)).map
        (ringedExtendedCech O r b).2) ≅
      Arrow.mk (ringedExtendedCech P r
        (fun i ↦ LocalizationRHom.restrictedSection (K := J) F O (b i))).2) := by
  let V := SheafOfModules.sliceCommModuleRestriction (J := J) F O
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
  induction r with
  | zero =>
    exact ⟨Arrow.isoMk (restrictionRingComplexIso (J := J) F O)
      (restrictionRingComplexIso (J := J) F O) (by
        dsimp only [ringedExtendedCech, Arrow.mk_hom]
        simp)⟩
  | succ r ih =>
    let X := (ringedExtendedCech O r (fun i ↦ b i.succ)).1
    let a := (ringedExtendedCech O r (fun i ↦ b i.succ)).2
    let X' := (ringedExtendedCech P r
      (fun i ↦ LocalizationRHom.restrictedSection (K := J) F O (b i.succ))).1
    let a' := (ringedExtendedCech P r
      (fun i ↦ LocalizationRHom.restrictedSection (K := J) F O (b i.succ))).2
    let T := actualTensor O
    let T' := actualTensor P
    let q := T.map (Prod.mkHom (ringedLocalizationTwoTermAugmentation O (b 0)) a)
    let q' := T'.map (Prod.mkHom (ringedLocalizationTwoTermAugmentation P
      (LocalizationRHom.restrictedSection (K := J) F O (b 0))) a')
    let u : T.obj (ringedSiteRingComplex O, ringedSiteRingComplex O) ≅
        ringedSiteRingComplex O := ringedKoszulUnitTensorIso O
    let u' : T'.obj (ringedSiteRingComplex P, ringedSiteRingComplex P) ≅
        ringedSiteRingComplex P := ringedKoszulUnitTensorIso P
    let c : Arrow.mk (Vc.map q) ≅ Arrow.mk q' :=
      tensorArrowRestriction T T' Vc (restrictionTensorComplexNatIso (J := J) F O)
        (hfactor (b 0)).some (ih (fun i ↦ b i.succ)).some
    let left : Arrow.mk (Vc.map (q ≫ u.hom)) ≅ Arrow.mk (Vc.map q) :=
      Arrow.isoMk (Iso.refl _) (Vc.mapIso u.symm) (by simp)
    let right : Arrow.mk q' ≅ Arrow.mk (q' ≫ u'.hom) :=
      Arrow.isoMk (Iso.refl _) u' (by simp)
    change Nonempty (Arrow.mk (Vc.map (ringedExtendedCech O (r + 1) b).2) ≅
      Arrow.mk (ringedExtendedCech P (r + 1)
        (fun i ↦ LocalizationRHom.restrictedSection (K := J) F O (b i))).2)
    exact ⟨left ≪≫ c ≪≫ right⟩

end RestrictionCalculation

private def derivedArrowRestriction
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {X Y : CochainComplex A ℤ} (a : X ⟶ Y) :
    Arrow.mk (R.mapDerivedCategory.map (DerivedCategory.Q.map a)) ≅
      Arrow.mk (DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map a)) :=
  Arrow.isoMk (R.mapDerivedCategoryFactors.app X) (R.mapDerivedCategoryFactors.app Y)
    (R.mapDerivedCategoryFactors.hom.naturality a).symm

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]

/-- Exact restriction carries the actual augmented Cech complex to the augmented
Cech complex of the restricted list, including further restrictions between slices.

Source: Stacks Project, sites-cohomology.tex, Tag 08JB; algebraization.tex, Tag 099E.
(auxiliary; not a blueprint node).

Proof: restriction of the localization presheaf is the localization presheaf of the
restricted section: both maps on fractions are the same universal localization lift.
Continuous cocontinuous slice restriction commutes with module sheafification, and
the comparison carries the section one to one. This identifies the two-term complex
[O -> O[1/b_i]] with its augmentation. Slice restriction commutes with tensor products,
finite sums and totalization, so induction on the ordered list gives an isomorphism
of augmented complexes. In the base case use restriction of the degree-zero ring
complex. Apply localization Q and the exact restriction factorization to obtain the
first arrow isomorphism. Repeat for Over.map f; on an object over V the denominator
is the same original section evaluated at that object's domain. Thus the further
restricted list is precisely the list displayed below, giving the second assertion.
All comparisons preserve the actual augmentation. The argument includes empty lists,
zero and invertible sections, and the zero ring. -/
theorem exists_ringed_augmented_cech_restriction :
    (∀ U : C, Nonempty
      (Arrow.mk ((ringedDerivedRestriction O U).map
          (DerivedCategory.Q.map (ringedExtendedCech O r b).2)) ≅
        Arrow.mk (DerivedCategory.Q.map
          (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedKoszulSliceSection O (b i) U)).2))) ∧
    (∀ (U V : C) (f : V ⟶ U), Nonempty
      (Arrow.mk ((ringedKoszulDerivedOverMap O f).map
          (DerivedCategory.Q.map
            (ringedExtendedCech (O.over U) r
              (fun i ↦ ringedKoszulSliceSection O (b i) U)).2)) ≅
        Arrow.mk (DerivedCategory.Q.map
          (ringedExtendedCech (O.over V) r
            (fun i ↦ ringedKoszulSliceSection O (b i) V)).2))) := by
  let (U : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  obtain ⟨ha, hb⟩ := exists_ringed_localization_factor_restriction O
  constructor
  · intro U
    let R := SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U
    have h := augmentedCechRestriction_of_factors
      (J := J.over U) (K := J) (Over.forget U) O (ha U) r b
    exact ⟨derivedArrowRestriction R (ringedExtendedCech O r b).2 ≪≫
      DerivedCategory.Q.mapArrow.mapIso h.some⟩
  · intro U V f
    let : HasDerivedCategory.{w} (SheafOfModules.{u}
        ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj
          (((Over.map f).sheafPushforwardContinuous CommRingCat
            (J.over V) (J.over U)).obj (O.over U)))) :=
      inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
        ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))))
    let R := SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) f
    have h := augmentedCechRestriction_of_factors
      (J := J.over V) (K := J.over U) (Over.map f) (O.over U) (hb U V f) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U)
    exact ⟨derivedArrowRestriction R
        (ringedExtendedCech (O.over U) r
          (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 ≪≫
      DerivedCategory.Q.mapArrow.mapIso h.some⟩

end CategoryTheory
