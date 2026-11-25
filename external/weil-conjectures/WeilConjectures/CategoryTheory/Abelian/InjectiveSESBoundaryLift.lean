/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison

/-!
# A simultaneous homotopy representative for split SES boundaries

Source: Stacks Project, Derived Categories, Tags 014Q and 0152.
(blueprint: lem-sc-p1-injective-ses-homotopy-boundary-lift).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- A degreewise split SES boundary has a homotopy representative that also
represents the canonical boundary after any additive functor.

Source: Stacks Project, Derived Categories, Tags 014Q and 0152.
(blueprint: lem-sc-p1-injective-ses-homotopy-boundary-lift).

Proof: Split the degree rows by injectivity of the first term, and form the
connecting chain map whose degree n component is section, differential,
retraction. Lift its homotopy class to the bounded below homotopy category,
using the inclusion's shift comparison. The split-SES boundary comparison
identifies its localization with the canonical source boundary. Map the row
splittings by v. The image connecting map equals the mapped source map followed
by the shift comparison: in each degree both are the image of section,
differential, retraction. The same split-SES boundary comparison in B identifies
its localization with the image SES boundary. Naturality and shift compatibility
of quotientCompQhIso give the two displayed endpoint equations. The construction
works also for zero complexes and arbitrary common lower bounds. -/
theorem injective_ses_homotopy_boundary_lift
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] (H : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (hvH : ((H.map (CochainComplex.plus A).ι).map
      (v.mapHomologicalComplex (.up ℤ))).ShortExact) :
    ∃ f : (HomotopyCategory.Plus.quotient A).obj H.X₃ ⟶
        ((HomotopyCategory.Plus.quotient A).obj H.X₁)⟦(1 : ℤ)⟧,
      ShiftedHom.map f (DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι) ≫
          ((DerivedCategory.quotientCompQhIso A).hom.app H.X₁.obj)⟦(1 : ℤ)⟧' =
        (DerivedCategory.quotientCompQhIso A).hom.app H.X₃.obj ≫
          DerivedCategory.triangleOfSESδ hH ∧
      ShiftedHom.map f
          ((v.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
            DerivedCategory.Plus.ι) ≫
          ((DerivedCategory.quotientCompQhIso B).hom.app
            ((v.mapHomologicalComplex (.up ℤ)).obj H.X₁.obj))⟦(1 : ℤ)⟧' =
        (DerivedCategory.quotientCompQhIso B).hom.app
            ((v.mapHomologicalComplex (.up ℤ)).obj H.X₃.obj) ≫
          DerivedCategory.triangleOfSESδ hvH := by
  let S := H.map (CochainComplex.plus A).ι
  let σ (n : ℤ) : (S.map (HomologicalComplex.eval A (.up ℤ) n)).Splitting :=
    by
      have : Injective ((S.map (HomologicalComplex.eval A (.up ℤ) n)).X₁) := by
        change Injective (H.X₁.obj.X n)
        infer_instance
      exact ShortComplex.ShortExact.splittingOfInjective
        ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hH n)
  let d := CochainComplex.homOfDegreewiseSplit S σ
  let d' : H.X₃ ⟶ H.X₁⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    (d ≫ ((CochainComplex.plus A).ι.commShiftIso (1 : ℤ)).inv.app H.X₁)
  let q := HomotopyCategory.Plus.quotient A
  let : q.CommShift ℤ := by
    dsimp [q, HomotopyCategory.Plus.quotient]
    infer_instance
  let f := ShiftedHom.map d' q
  refine ⟨f, ?_, ?_⟩
  · let e₁ := HomotopyCategory.Plus.quotientCompιIso A
    let e₂ := DerivedCategory.Plus.QhCompιIsoιCompQh A
    have : NatTrans.CommShift e₁.hom ℤ := by
      dsimp [e₁, HomotopyCategory.Plus.quotientCompιIso]
      infer_instance
    have : NatTrans.CommShift e₂.hom ℤ := by
      change NatTrans.CommShift
        ((DerivedCategory.TStructure.t (C := A)).plus.liftCompιIso
          (HomotopyCategory.Plus.ι A ⋙ DerivedCategory.Qh) _).hom ℤ
      infer_instance
    let e : (q ⋙ DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι ≅
        (CochainComplex.plus A).ι ⋙ DerivedCategory.Q :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft q e₂ ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e₁ DerivedCategory.Qh ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (CochainComplex.plus A).ι
          (DerivedCategory.quotientCompQhIso A)
    have : NatTrans.CommShift e.hom ℤ := by dsimp [e]; infer_instance
    have hn := ShiftedHom.map_naturality d' e.hom
    simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hn
    rw [DerivedCategory.triangleOfSESδ_eq_degreewiseSplit S hH σ]
    have hd : ShiftedHom.map d' (CochainComplex.plus A).ι = d := by
      change (d ≫ _) ≫ _ = d
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    simp only [ShiftedHom.comp_map] at hn
    rw [hd] at hn
    have he (K : CochainComplex.Plus A) : e.hom.app K =
        (DerivedCategory.quotientCompQhIso A).hom.app K.obj := by
      dsimp [e, e₁, e₂, HomotopyCategory.Plus.quotientCompιIso,
        DerivedCategory.Plus.QhCompιIsoιCompQh, ObjectProperty.liftCompιIso]
      repeat first | erw [Category.id_comp] | erw [Functor.map_id]
    rw [he, he] at hn
    simpa only [f, d, ShiftedHom.comp_map] using hn
  · let σv (n : ℤ) : ((S.map (v.mapHomologicalComplex (.up ℤ))).map
        (HomologicalComplex.eval B (.up ℤ) n)).Splitting := (σ n).map v
    have hdv : ShiftedHom.map d (v.mapHomologicalComplex (.up ℤ)) =
        CochainComplex.homOfDegreewiseSplit (S.map (v.mapHomologicalComplex (.up ℤ)))
          σv := by
      ext n
      simp [ShiftedHom.map, d, CochainComplex.cocycleOfDegreewiseSplit, σv,
        Functor.map_comp]
    let e₁ := HomotopyCategory.Plus.quotientCompιIso A
    let e₂ := DerivedCategory.Plus.QhCompιIsoιCompQh B
    let e₃ : v.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
        HomotopyCategory.Plus.ι A ⋙ v.mapHomotopyCategory (.up ℤ) := Iso.refl _
    have : NatTrans.CommShift e₁.hom ℤ := by
      dsimp [e₁, HomotopyCategory.Plus.quotientCompιIso]
      infer_instance
    have : NatTrans.CommShift e₂.hom ℤ := by
      change NatTrans.CommShift
        ((DerivedCategory.TStructure.t (C := B)).plus.liftCompιIso
          (HomotopyCategory.Plus.ι B ⋙ DerivedCategory.Qh) _).hom ℤ
      infer_instance
    have : NatTrans.CommShift e₃.hom ℤ := by
      change NatTrans.CommShift
        ((HomotopyCategory.plus B).liftCompιIso
          (HomotopyCategory.Plus.ι A ⋙ v.mapHomotopyCategory (.up ℤ)) _).hom ℤ
      infer_instance
    let eh : (v.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        DerivedCategory.Plus.ι ≅
        (HomotopyCategory.Plus.ι A ⋙ v.mapHomotopyCategory (.up ℤ)) ⋙
          DerivedCategory.Qh :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft v.mapHomotopyCategoryPlus e₂ ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₃ DerivedCategory.Qh
    let eq : q ⋙ (HomotopyCategory.Plus.ι A ⋙ v.mapHomotopyCategory (.up ℤ)) ≅
        ((CochainComplex.plus A).ι ⋙ v.mapHomologicalComplex (.up ℤ)) ⋙
          HomotopyCategory.quotient B (.up ℤ) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e₁ (v.mapHomotopyCategory (.up ℤ)) ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (CochainComplex.plus A).ι
          (v.mapHomotopyCategoryFactors (.up ℤ)) ≪≫ (Functor.associator _ _ _).symm
    let e : q ⋙ ((v.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        DerivedCategory.Plus.ι) ≅
        ((CochainComplex.plus A).ι ⋙ v.mapHomologicalComplex (.up ℤ)) ⋙
          DerivedCategory.Q :=
      Functor.isoWhiskerLeft q eh ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eq DerivedCategory.Qh ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
    have : NatTrans.CommShift eh.hom ℤ := by dsimp [eh]; infer_instance
    have : NatTrans.CommShift eq.hom ℤ := by dsimp [eq]; infer_instance
    have : NatTrans.CommShift e.hom ℤ := by dsimp [e]; infer_instance
    have hn := ShiftedHom.map_naturality d' e.hom
    simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hn
    have hd : ShiftedHom.map d' (CochainComplex.plus A).ι = d := by
      change (d ≫ _) ≫ _ = d
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    simp only [ShiftedHom.comp_map] at hn
    rw [hd, hdv] at hn
    rw [DerivedCategory.triangleOfSESδ_eq_degreewiseSplit _ hvH σv]
    have he (K : CochainComplex.Plus A) : e.hom.app K =
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((v.mapHomologicalComplex (.up ℤ)).obj K.obj) := by
      dsimp [e, eh, eq, e₁, e₂, e₃, HomotopyCategory.Plus.quotientCompιIso,
        DerivedCategory.Plus.QhCompιIsoιCompQh, ObjectProperty.liftCompιIso,
        Functor.mapHomotopyCategoryFactors]
      repeat first | erw [Category.id_comp] | erw [Category.comp_id] |
        erw [Functor.map_id]
    rw [he, he] at hn
    simpa only [f, ShiftedHom.comp_map, Functor.map_id, Category.id_comp,
      Category.comp_id] using hn

end CategoryTheory
