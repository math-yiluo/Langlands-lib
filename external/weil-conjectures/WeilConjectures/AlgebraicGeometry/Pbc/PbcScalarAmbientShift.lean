/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarComposition
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Counit-normalized ambient scalar shift

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section ScalarShift
attribute [local irreducible] completedAdicDerivedChange
variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) (T : Scheme.{u})

private theorem pbcKanCommShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

-- The comparison determines the shift structure by Kan uniqueness, degree by degree.
private theorem pbcRightKanShift_unique
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    {E : Type*} [Category* E] [HasShift E ℤ]
    (F : C ⥤ E) [F.CommShift ℤ] (Q : C ⥤ D) [Q.CommShift ℤ]
    (LF : D ⥤ E) (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α]
    (s t : LF.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift α ℤ)
    (ht : letI := t; NatTrans.CommShift α ℤ) : s = t := by
  have square (q : LF.CommShift ℤ) (hq : letI := q; NatTrans.CommShift α ℤ)
      (n : ℤ) (X : C) :
      LF.map ((Q.commShiftIso n).hom.app X) ≫
          (Functor.commShiftIso LF (self := q) n).hom.app (Q.obj X) ≫
            (shiftFunctor E n).map (α.app X) =
        α.app ((shiftFunctor C n).obj X) ≫ (F.commShiftIso n).hom.app X := by
    let := q
    have := hq
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α n X
  have he (n : ℤ) : Functor.commShiftIso LF (self := s) n =
      Functor.commShiftIso LF (self := t) n := by
    let H := shiftFunctor E n
    let P := Functor.RightExtension.postcompose₂ Q F H
    let : IsIso (𝟙 (F ⋙ H)) := inferInstance
    let : P.IsEquivalence := by
      dsimp [P, Functor.RightExtension.postcompose₂]
      let a : ((Functor.whiskeringRight D E E).obj H) ⋙
          (Functor.whiskeringLeft C D E).obj Q ⟶
          (Functor.whiskeringLeft C D E).obj Q ⋙
            ((Functor.whiskeringRight C E E).obj H) :=
        { app G := (Functor.associator Q G H).inv }
      let : IsIso a := by apply NatIso.isIso_of_isIso_app
      exact CostructuredArrow.isEquivalenceMap₂ a (𝟙 _)
    let γ := (Functor.associator Q LF H).inv ≫ whiskerRight α H
    have : (LF ⋙ H).IsRightKanExtension γ := by
      constructor
      refine ⟨IsTerminal.ofIso
        (IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
      exact Functor.RightExtension.postcompose₂ObjMkIso H α
    apply Iso.ext
    apply (LF ⋙ H).hom_ext_of_isRightKanExtension γ
    ext X
    simp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
    apply (cancel_epi (LF.map ((Q.commShiftIso n).hom.app X))).1
    simpa only [Category.assoc] using (square s hs n X).trans (square t ht n X).symm
  exact pbcKanCommShift_ext s t he

set_option linter.unusedVariables false in
/-- Universal tensor counits uniquely fix the termwise derived shift comparison. -/
theorem pbcAmbientScalarShift_exists :
    ∃! q : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ,
      (fun [qInst : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ] ↦
        NatTrans.CommShift (pbcExtensionCounit (pbcScalarCoefficientMap l E F i T)) ℤ)
          (qInst := q) := by
  let φ := pbcScalarCoefficientMap l E F i T
  have := pbcDerivedExtension_universal φ
  have hkan := CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension
    (pbcDerivedExtend φ) (pbcExtensionCounit φ)
    (HomotopyCategory.quasiIso
      (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) (.up ℤ))
  have := hkan
  obtain ⟨q, hq⟩ := CategoryTheory.Functor.rightKanExtension_coherentShift _
    DerivedCategory.Qh (pbcDerivedExtend φ) (pbcExtensionCounit φ) hkan
  exact ⟨q, hq, fun q' hq' ↦ pbcRightKanShift_unique _ _ _ _ q' q hq' hq⟩

/-- The tensor shift comparison normalized by its actual derived counit. -/
instance pbcAmbientScalarShift : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ :=
  (pbcAmbientScalarShift_exists l E F i T).exists.choose

section NormalizedScalarAdjunctionShift
attribute [local irreducible] pbcDerivedScalarAdjunction

private local instance scalarRestrictionShift
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedRestrict φ).CommShift ℤ :=
  inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarAdjunction_complexUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (L : A ⥤ B) (R : B ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : L ⊣ R) (LD : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (d : LD ⊣ R.mapDerivedCategory)
    (hd : ∀ H, d.unit.app (DerivedCategory.Qh.obj H) ≫ R.mapDerivedCategory.map (ε.app H) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj H) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app H))
    (P : CochainComplex A ℤ) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map
          (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
            ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
            DerivedCategory.Qh.map
              ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
            (DerivedCategory.quotientCompQhIso _).hom.app
              ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) := by
  have hp := hd ((HomotopyCategory.quotient _ _).obj P)
  change d.unit.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
    R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
    R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient B (.up ℤ)).obj
      ((L.mapHomologicalComplex (.up ℤ)).obj P)) = _ at hp
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hp
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, Functor.map_id,
    Category.id_comp, Category.comp_id] at hp ⊢
  erw [LD.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [R.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.comp_id,
    Category.comp_id] at hp
  erw [Category.comp_id]
  erw [Category.id_comp] at hp
  exact hp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarAdjunction_shift :
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i T)).CommShift ℤ := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let φ := pbcScalarCoefficientMap l E F i T
  let L := pbcExtend φ
  let R := pbcRestrict φ
  let LD := pbcDerivedExtend φ
  let ε := pbcExtensionCounit φ
  let adj := pbcScalarAdjunction φ
  have hLD := pbcDerivedExtension_universal φ
  have hr (X : HomotopyCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
      (.up ℤ)) :
      ∃ (K : HomotopyCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
          (.up ℤ)) (f : K ⟶ X),
        IsIso (ε.app K) ∧ HomotopyCategory.quasiIso _ (.up ℤ) f := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, f, hK, hf⟩ :=
      ScalarReductionDerivedProof.kFlatResolutions.{u + 1, u, u + 1}
        (J := ProEt.topology T) (O := pbcAdicCompletion T (pbcIntegralDatum l E)) P
    exact ⟨_, (HomotopyCategory.quotient _ _).map f,
      pbcExtensionCounit_isIso φ K hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  obtain ⟨d, hd⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    L R adj LD ε hLD hr
  have hn (P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
      d.unit.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) := by
    exact scalarAdjunction_complexUnit L R adj LD ε d hd P
  have he : d = pbcDerivedScalarAdjunction φ := by
    unfold pbcDerivedScalarAdjunction
    exact (pbcDerivedScalarAdjunction_exists φ).unique
      (fun P _ ↦ hn P) (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec
  have : LD.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension LD ε
      (HomotopyCategory.quasiIso _ (.up ℤ))
  have : NatTrans.CommShift ε ℤ :=
    (pbcAmbientScalarShift_exists l E F i T).exists.choose_spec
  have hu : NatTrans.CommShift d.unit ℤ := by
    apply CategoryTheory.normalized_unit_commShift DerivedCategory.Qh DerivedCategory.Qh
      (L.mapHomotopyCategory (.up ℤ)) (R.mapHomotopyCategory (.up ℤ))
      LD R.mapDerivedCategory (adj.mapHomotopyCategory (.up ℤ)) d
      ε R.mapDerivedCategoryFactorsh.inv
    intro H
    apply (cancel_mono (R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj H))).mp
    simpa only [Functor.comp_obj, Functor.id_obj, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id] using hd H
  rw [he] at hu
  exact Adjunction.CommShift.mk' _ ℤ hu

end NormalizedScalarAdjunctionShift

end ScalarShift
end AlgebraicGeometry.Scheme
