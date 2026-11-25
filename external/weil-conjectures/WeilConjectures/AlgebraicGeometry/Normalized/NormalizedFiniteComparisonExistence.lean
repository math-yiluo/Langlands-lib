/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteComparisonModels
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated

/-!
# Existence of normalized finite completed-ring comparisons

The source and target comparisons are specified by their counit equations on
K-flat representatives. Uniqueness is proved separately in the parent module.

## References

* Stacks 099N, 03DI, 06XN
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint Functor.mapDerivedCategoryFactorsh Functor.mapHomotopyCategory
  Functor.mapHomotopyCategoryFactors

attribute [local irreducible] completedReductionTower
  completedReductionTowerCounit completedTowerPullbackCounit pbcExtensionCounit
  completedAdicDerivedChange Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  limit AdicCoefficients.ringSystem completedAdicChange completedReductionModuleTowerFunctor
  completedTowerModulePullback cbcStrictOpenModule cbcSourceLevel cbcTargetLevel

attribute [local instance] cbcStrictOpenModule_additive completedTowerModulePullback_additive
  completedReductionModuleTowerFunctor_additive cbcSourceLevel_preservesZeroMorphisms
  cbcTargetLevel_preservesZeroMorphisms cbcFiniteSourceModel_preservesZeroMorphisms
  cbcFiniteTargetModel_preservesZeroMorphisms

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

private def homotopyFactors
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (E : C ⥤ D) [E.Additive] :
    HomotopyCategory.quotient C (.up ℤ) ⋙
        (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)

private theorem descentComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (S : CochainComplex C ℤ → Prop)
    (res : ∀ K : CochainComplex C ℤ,
      ∃ (P : CochainComplex C ℤ) (s : P ⟶ K), S P ∧ QuasiIso s)
    (F G : DerivedCategory C ⥤ DerivedCategory D) (E : C ⥤ D) [E.Additive]
    (α : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β : DerivedCategory.Q ⋙ G ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hα : ∀ P, S P → IsIso (α.app P))
    (hβ : ∀ P, S P → IsIso (β.app P)) :
    ∃ e : F ≅ G, ∀ P, S P →
      α.app P = e.hom.app (DerivedCategory.Q.obj P) ≫ β.app P := by
  classical
  let q := HomotopyCategory.quotient C (.up ℤ)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let i := DerivedCategory.quotientCompQhIso C
  let j := homotopyFactors E
  let pre := (Functor.whiskeringLeft _ _ (DerivedCategory D)).obj q
  let a : DerivedCategory.Qh ⋙ F ⟶ H := pre.preimage
    (Functor.whiskerRight i.hom F ≫ α ≫ j.inv)
  let b : DerivedCategory.Qh ⋙ G ⟶ H := pre.preimage
    (Functor.whiskerRight i.hom G ≫ β ≫ j.inv)
  have ha (P : CochainComplex C ℤ) :
      a.app (q.obj P) = F.map (i.hom.app P) ≫ α.app P ≫ j.inv.app P :=
    congr_app (pre.map_preimage _) P
  have hb (P : CochainComplex C ℤ) :
      b.app (q.obj P) = G.map (i.hom.app P) ≫ β.app P ≫ j.inv.app P :=
    congr_app (pre.map_preimage _) P
  let R : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
    fun K ↦ ∃ P : CochainComplex C ℤ, S P ∧ q.obj P = K
  have hr (K : HomotopyCategory C (.up ℤ)) :
      ∃ (P : R.FullSubcategory) (s : P.obj ⟶ K), W s := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨P, s, hP, hs⟩ := res K
    exact ⟨⟨q.obj P, P, hP, rfl⟩, q.map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let : W.HasRightCalculusOfFractions :=
    (HomotopyCategory.quasiIso_saturated_triangulated C).2.1
  let L := R.ι ⋙ DerivedCategory.Qh
  let V := W.inverseImage R.ι
  let : L.IsLocalization V := SheafOfModules.restriction_localization W
    DerivedCategory.Qh R hr
  have hiA : ∀ K : R.FullSubcategory, IsIso ((Functor.whiskerLeft R.ι a).app K) := by
    intro K
    obtain ⟨P, hP, heq⟩ := K.property
    change IsIso (a.app K.obj)
    rw [← heq, ha]
    let := hα P hP
    infer_instance
  have hiB : ∀ K : R.FullSubcategory, IsIso ((Functor.whiskerLeft R.ι b).app K) := by
    intro K
    obtain ⟨P, hP, heq⟩ := K.property
    change IsIso (b.app K.obj)
    rw [← heq, hb]
    let := hβ P hP
    infer_instance
  let : IsIso (Functor.whiskerLeft R.ι a) := NatIso.isIso_of_isIso_app _
  let : IsIso (Functor.whiskerLeft R.ι b) := NatIso.isIso_of_isIso_app _
  let z : L ⋙ F ≅ L ⋙ G :=
    asIso (Functor.whiskerLeft R.ι a) ≪≫ (asIso (Functor.whiskerLeft R.ι b)).symm
  let e := Localization.liftNatIso L V (L ⋙ F) (L ⋙ G) F G z
  refine ⟨e, ?_⟩
  intro P hP
  let K : R.FullSubcategory := ⟨q.obj P, P, hP, rfl⟩
  have hzK (N : R.FullSubcategory) :
      e.hom.app (L.obj N) ≫ b.app N.obj = a.app N.obj := by
    have : IsIso (b.app N.obj) := hiB N
    simp only [e, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Category.comp_id, z, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, asIso_hom, asIso_inv, NatIso.isIso_inv_app,
      Functor.whiskerLeft_app, Category.assoc]
    change a.app N.obj ≫ inv (b.app N.obj) ≫ b.app N.obj = a.app N.obj
    rw [IsIso.inv_hom_id, Category.comp_id]
  have hz := hzK K
  rw [ha, hb] at hz
  have hn := e.hom.naturality (i.hom.app P)
  change F.map (i.hom.app P) ≫ e.hom.app (DerivedCategory.Q.obj P) =
    e.hom.app (L.obj K) ≫ G.map (i.hom.app P) at hn
  rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc, Category.assoc] at hz
  have hh : e.hom.app (DerivedCategory.Q.obj P) ≫ β.app P = α.app P := by
    apply (cancel_epi (F.map (i.hom.app P))).1
    apply (cancel_mono (j.inv.app P)).1
    simpa only [Category.assoc] using hz
  exact hh.symm

private def complexCounit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := Functor.leftDerivedCounitOnComplex E F ε P
  naturality P P' s := by
    let τ := Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv F ≫
      Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε ≫
        (homotopyFactors E).hom
    simpa only [τ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, homotopyFactors, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Category.assoc, Functor.leftDerivedCounitOnComplex] using
        τ.naturality s

private theorem complexCounit_app_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ)
    (h : IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))) :
    IsIso ((complexCounit E F ε).app P) := by
  let := h
  dsimp only [complexCounit, Functor.leftDerivedCounitOnComplex]
  infer_instance

private def composeCounits
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory E)
    (α : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (LF ⋙ LG) ⟶
      (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight α LG ≫ Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) β

private theorem composeCounits_app_isIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory E)
    (α : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex C ℤ) (hα : IsIso (α.app P))
    (hβ : IsIso (β.app ((F.mapHomologicalComplex (.up ℤ)).obj P))) :
    IsIso ((composeCounits F G LF LG α β).app P) := by
  let := hα
  let := hβ
  change IsIso (LG.map (α.app P) ≫ β.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
  infer_instance

private def composeFourCounits
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] (F₁ : C₁ ⥤ C₂) [F₁.Additive]
    (F₂ : C₂ ⥤ C₃) [F₂.Additive] (F₃ : C₃ ⥤ C₄) [F₃.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory C₁)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (L₃ : DerivedCategory C₃ ⥤ DerivedCategory C₄)
    (α₀ : DerivedCategory.Q ⋙ L₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₁ : DerivedCategory.Q ⋙ L₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₂ : DerivedCategory.Q ⋙ L₂ ⟶ F₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₃ : DerivedCategory.Q ⋙ L₃ ⟶ F₃.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (L₀ ⋙ L₁ ⋙ L₂ ⋙ L₃) ⟶
      (F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  composeCounits F₀ (F₁ ⋙ F₂ ⋙ F₃) L₀ (L₁ ⋙ L₂ ⋙ L₃) α₀
    (composeCounits F₁ (F₂ ⋙ F₃) L₁ (L₂ ⋙ L₃) α₁
      (composeCounits F₂ F₃ L₂ L₃ α₂ α₃))

private theorem composeFourCounits_app_isIso
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] (F₁ : C₁ ⥤ C₂) [F₁.Additive]
    (F₂ : C₂ ⥤ C₃) [F₂.Additive] (F₃ : C₃ ⥤ C₄) [F₃.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory C₁)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (L₃ : DerivedCategory C₃ ⥤ DerivedCategory C₄)
    (α₀ : DerivedCategory.Q ⋙ L₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₁ : DerivedCategory.Q ⋙ L₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₂ : DerivedCategory.Q ⋙ L₂ ⟶ F₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₃ : DerivedCategory.Q ⋙ L₃ ⟶ F₃.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex C₀ ℤ) (h₀ : IsIso (α₀.app P))
    (h₁ : IsIso (α₁.app ((F₀.mapHomologicalComplex (.up ℤ)).obj P)))
    (h₂ : IsIso (α₂.app ((F₁.mapHomologicalComplex (.up ℤ)).obj
      ((F₀.mapHomologicalComplex (.up ℤ)).obj P))))
    (h₃ : IsIso (α₃.app ((F₂.mapHomologicalComplex (.up ℤ)).obj
      ((F₁.mapHomologicalComplex (.up ℤ)).obj
        ((F₀.mapHomologicalComplex (.up ℤ)).obj P))))) :
    IsIso ((composeFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃).app P) := by
  unfold composeFourCounits
  apply composeCounits_app_isIso
  · exact h₀
  · apply composeCounits_app_isIso
    · exact h₁
    · exact composeCounits_app_isIso _ _ _ _ _ _ _ h₂ h₃

private theorem composeFourCounits_app
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] (F₁ : C₁ ⥤ C₂) [F₁.Additive]
    (F₂ : C₂ ⥤ C₃) [F₂.Additive] (F₃ : C₃ ⥤ C₄) [F₃.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory C₁)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (L₃ : DerivedCategory C₃ ⥤ DerivedCategory C₄)
    (α₀ : DerivedCategory.Q ⋙ L₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₁ : DerivedCategory.Q ⋙ L₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₂ : DerivedCategory.Q ⋙ L₂ ⟶ F₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₃ : DerivedCategory.Q ⋙ L₃ ⟶ F₃.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex C₀ ℤ) :
    (composeFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃).app P =
      L₃.map (L₂.map (L₁.map (α₀.app P) ≫
        α₁.app ((F₀.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          α₂.app ((F₁.mapHomologicalComplex (.up ℤ)).obj
            ((F₀.mapHomologicalComplex (.up ℤ)).obj P))) ≫
        α₃.app ((F₂.mapHomologicalComplex (.up ℤ)).obj
          ((F₁.mapHomologicalComplex (.up ℤ)).obj
            ((F₀.mapHomologicalComplex (.up ℤ)).obj P))) := by
  simp only [composeFourCounits, composeCounits, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]

private def coordinateFourCounits
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] (F₁ : C₁ ⥤ C₂) [F₁.Additive]
    (F₂ : C₂ ⥤ C₃) [F₂.Additive] (F₃ : C₃ ⥤ C₄) [F₃.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory C₁)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (L₃ : DerivedCategory C₃ ⥤ DerivedCategory C₄)
    (α₀ : DerivedCategory.Q ⋙ L₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₁ : DerivedCategory.Q ⋙ L₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₂ : DerivedCategory.Q ⋙ L₂ ⟶ F₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₃ : DerivedCategory.Q ⋙ L₃ ⟶ F₃.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K : C₀ ⥤ C₄) [K.PreservesZeroMorphisms]
    (γ : (F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      K.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (L₀ ⋙ L₁ ⋙ L₂ ⋙ L₃) ⟶
      K.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P :=
    L₃.map (L₂.map (L₁.map (α₀.app P) ≫
      α₁.app ((F₀.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        α₂.app ((F₁.mapHomologicalComplex (.up ℤ)).obj
          ((F₀.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      α₃.app ((F₂.mapHomologicalComplex (.up ℤ)).obj
        ((F₁.mapHomologicalComplex (.up ℤ)).obj
          ((F₀.mapHomologicalComplex (.up ℤ)).obj P))) ≫ γ.app P
  naturality P P' f := by
    let τ := composeFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃ ≫ γ
    simpa only [τ, NatTrans.comp_app, composeFourCounits_app, Category.assoc]
      using τ.naturality f

private theorem coordinateFourCounits_app_isIso
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] (F₁ : C₁ ⥤ C₂) [F₁.Additive]
    (F₂ : C₂ ⥤ C₃) [F₂.Additive] (F₃ : C₃ ⥤ C₄) [F₃.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory C₁)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (L₃ : DerivedCategory C₃ ⥤ DerivedCategory C₄)
    (α₀ : DerivedCategory.Q ⋙ L₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₁ : DerivedCategory.Q ⋙ L₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₂ : DerivedCategory.Q ⋙ L₂ ⟶ F₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₃ : DerivedCategory.Q ⋙ L₃ ⟶ F₃.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K : C₀ ⥤ C₄) [K.PreservesZeroMorphisms]
    (γ : (F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      K.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex C₀ ℤ)
    (h : IsIso ((composeFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃).app P))
    (hγ : IsIso (γ.app P)) :
    IsIso ((coordinateFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃ K γ).app P) := by
  let := h
  let := hγ
  have hh : IsIso (((composeFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃) ≫ γ).app P) :=
    by
      change IsIso ((composeFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃).app P ≫
        γ.app P)
      infer_instance
  simpa only [coordinateFourCounits, NatTrans.comp_app, composeFourCounits_app,
    Category.assoc] using hh

private theorem coordinateFourCounits_components_isIso
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] (F₁ : C₁ ⥤ C₂) [F₁.Additive]
    (F₂ : C₂ ⥤ C₃) [F₂.Additive] (F₃ : C₃ ⥤ C₄) [F₃.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory C₁)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (L₃ : DerivedCategory C₃ ⥤ DerivedCategory C₄)
    (α₀ : DerivedCategory.Q ⋙ L₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₁ : DerivedCategory.Q ⋙ L₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₂ : DerivedCategory.Q ⋙ L₂ ⟶ F₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₃ : DerivedCategory.Q ⋙ L₃ ⟶ F₃.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K : C₀ ⥤ C₄) [K.PreservesZeroMorphisms]
    (γ : (F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      K.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex C₀ ℤ)
    (h₀ : IsIso (α₀.app P))
    (h₁ : IsIso (α₁.app ((F₀.mapHomologicalComplex (.up ℤ)).obj P)))
    (h₂ : IsIso (α₂.app ((F₁.mapHomologicalComplex (.up ℤ)).obj
      ((F₀.mapHomologicalComplex (.up ℤ)).obj P))))
    (h₃ : IsIso (α₃.app ((F₂.mapHomologicalComplex (.up ℤ)).obj
      ((F₁.mapHomologicalComplex (.up ℤ)).obj
        ((F₀.mapHomologicalComplex (.up ℤ)).obj P)))))
    (hγ : IsIso (γ.app P)) :
    IsIso ((coordinateFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃ K γ).app P) := by
  exact coordinateFourCounits_app_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (composeFourCounits_app_isIso _ _ _ _ _ _ _ _ _ _ _ _ P h₀ h₁ h₂ h₃) hγ

private theorem mapComplexIso_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory D] {E F : C ⥤ D}
    [E.PreservesZeroMorphisms] [F.PreservesZeroMorphisms]
    (e : E ≅ F) (P : CochainComplex C ℤ) :
    IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P)) := by
  change IsIso (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).app P).hom)
  infer_instance

private theorem descentFourComparison
    {C₀ C₁ C₂ C₃ C₄ B : Type*}
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] (F₁ : C₁ ⥤ C₂) [F₁.Additive]
    (F₂ : C₂ ⥤ C₃) [F₂.Additive] (F₃ : C₃ ⥤ C₄) [F₃.Additive]
    (L₀ : DerivedCategory C₀ ⥤ DerivedCategory C₁)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (L₃ : DerivedCategory C₃ ⥤ DerivedCategory C₄)
    (α₀ : DerivedCategory.Q ⋙ L₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₁ : DerivedCategory.Q ⋙ L₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₂ : DerivedCategory.Q ⋙ L₂ ⟶ F₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α₃ : DerivedCategory.Q ⋙ L₃ ⟶ F₃.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (J₀ : C₀ ⥤ B) [J₀.Additive] (J₁ : B ⥤ C₄) [J₁.Additive]
    (eK : (F₀ ⋙ F₁ ⋙ F₂ ⋙ F₃) ≅ J₀ ⋙ J₁)
    (M₀ : DerivedCategory C₀ ⥤ DerivedCategory B)
    (M₁ : DerivedCategory B ⥤ DerivedCategory C₄)
    (β₀ : DerivedCategory.Q ⋙ M₀ ⟶ J₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (β₁ : DerivedCategory.Q ⋙ M₁ ⟶ J₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (S : CochainComplex C₀ ℤ → Prop)
    (res : ∀ M : CochainComplex C₀ ℤ,
      ∃ (P : CochainComplex C₀ ℤ) (s : P ⟶ M), S P ∧ QuasiIso s)
    (h₀ : ∀ P, S P → IsIso (α₀.app P))
    (h₁ : ∀ P, S P → IsIso (α₁.app ((F₀.mapHomologicalComplex (.up ℤ)).obj P)))
    (h₂ : ∀ P, S P → IsIso (α₂.app ((F₁.mapHomologicalComplex (.up ℤ)).obj
      ((F₀.mapHomologicalComplex (.up ℤ)).obj P))))
    (h₃ : ∀ P, S P → IsIso (α₃.app ((F₂.mapHomologicalComplex (.up ℤ)).obj
      ((F₁.mapHomologicalComplex (.up ℤ)).obj
        ((F₀.mapHomologicalComplex (.up ℤ)).obj P)))))
    (hβ₀ : ∀ P, S P → IsIso (β₀.app P))
    (hβ₁ : ∀ P, S P → IsIso (β₁.app ((J₀.mapHomologicalComplex (.up ℤ)).obj P))) :
    ∃ e : (L₀ ⋙ L₁ ⋙ L₂ ⋙ L₃) ≅ M₀ ⋙ M₁, ∀ P, S P →
      HEq
        (L₃.map (L₂.map (L₁.map (α₀.app P) ≫
          α₁.app ((F₀.mapHomologicalComplex (.up ℤ)).obj P)) ≫
            α₂.app ((F₁.mapHomologicalComplex (.up ℤ)).obj
              ((F₀.mapHomologicalComplex (.up ℤ)).obj P))) ≫
          α₃.app ((F₂.mapHomologicalComplex (.up ℤ)).obj
            ((F₁.mapHomologicalComplex (.up ℤ)).obj
              ((F₀.mapHomologicalComplex (.up ℤ)).obj P))) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex eK.hom (.up ℤ)).app P))
        (e.hom.app (DerivedCategory.Q.obj P) ≫ M₁.map (β₀.app P) ≫
          β₁.app ((J₀.mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨e, he⟩ := descentComparison S res (L₀ ⋙ L₁ ⋙ L₂ ⋙ L₃) (M₀ ⋙ M₁) (J₀ ⋙ J₁)
    (coordinateFourCounits F₀ F₁ F₂ F₃ L₀ L₁ L₂ L₃ α₀ α₁ α₂ α₃ (J₀ ⋙ J₁)
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex eK.hom (.up ℤ)) DerivedCategory.Q))
    (composeCounits J₀ J₁ M₀ M₁ β₀ β₁)
    (fun P hP ↦ coordinateFourCounits_components_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
      (h₀ P hP) (h₁ P hP) (h₂ P hP) (h₃ P hP) (mapComplexIso_isIso eK P))
    (fun P hP ↦ composeCounits_app_isIso _ _ _ _ _ _ P (hβ₀ P hP) (hβ₁ P hP))
  refine ⟨e, ?_⟩
  intro P hP
  exact heq_of_eq (he P hP)

private theorem exactLeftAdjointToEquivalence
    {C D : Type*} [Category C] [Category D] (E : D ≌ C) (F : C ⥤ D)
    (a : F ⊣ E.functor) : PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  let t := a.leftAdjointUniq E.symm.toAdjunction
  refine ⟨preservesFiniteLimits_of_natIso t.symm, ?_⟩
  let : PreservesColimitsOfSize.{0, 0} F := a.leftAdjoint_preservesColimits
  infer_instance

private theorem completedPullback_exact {S T : Scheme.{u}} (f : S ⟶ T) :
    PreservesFiniteLimits (completedModulePullback f d) ∧
      PreservesFiniteColimits (completedModulePullback f d) := by
  let h := completedCoefficient_isIso f d
  let c := asIso (completedCoefficientMap f d)
  let rc := (adicLisseForget S).mapIso c
  let e := proEtaleScalarEquivalence S rc
  let a := adicDatumOrdinaryAdjunction S c.hom
  obtain ⟨hl, hc⟩ := exactLeftAdjointToEquivalence e (reductionChange S c.hom) a
  have : PreservesFiniteLimits (reductionChange S (completedCoefficientMap f d)) := by
    simpa only [c, asIso_hom] using hl
  have : PreservesFiniteColimits (reductionChange S (completedCoefficientMap f d)) := by
    simpa only [c, asIso_hom] using hc
  have : PreservesFiniteLimits (proEtaleModuleInverseImage f (pbcAdicCompletion T d)) :=
    proEtaleModuleInverseImage_preservesFiniteLimits f _
  have : PreservesFiniteColimits (proEtaleModuleInverseImage f (pbcAdicCompletion T d)) :=
    let : PreservesColimitsOfSize.{0, 0}
        (proEtaleModuleInverseImage f (pbcAdicCompletion T d)) :=
      (proEtaleModuleInverseImageAdjunction f _).leftAdjoint_preservesColimits
    inferInstance
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

private theorem exactCounit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))) : IsIso ε := by
  let := hF
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts F ε
    (W := HomotopyCategory.quasiIso C (.up ℤ))
  intro K L s hs
  have : IsIso (DerivedCategory.Qh.map s) := Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) s hs
  exact (NatIso.isIso_map_iff E.mapDerivedCategoryFactorsh s).1 (by
    change IsIso (E.mapDerivedCategory.map (DerivedCategory.Qh.map s))
    infer_instance)

private theorem towerPullback_counit_iso {S T : Scheme.{u}} (f : S ⟶ T) :
    IsIso (completedTowerPullbackCounit f d) := by
  obtain ⟨hl, hc⟩ := completedPullback_exact d f
  let := hl
  let := hc
  have : PreservesFiniteLimits (completedTowerModulePullback f d) := by
    unfold completedTowerModulePullback
    exact ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits (completedTowerModulePullback f d) := by
    unfold completedTowerModulePullback
    exact ⟨fun _ _ _ ↦ inferInstance⟩
  have hLF : (completedTowerPullback f d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit f d)
      (HomotopyCategory.quasiIso (pbcTowers T (pbcAdicCompletion T d)) (.up ℤ)) :=
    by
      unfold completedTowerPullback completedTowerPullbackCounit
      exact (completedTowerPullback_exists f d).choose_spec.choose_spec.1
  exact exactCounit_isIso (completedTowerModulePullback f d)
    (completedTowerPullback f d) (completedTowerPullbackCounit f d) hLF

attribute [local irreducible] complexCounit composeCounits composeFourCounits
  coordinateFourCounits

private def reductionCounitNT (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ completedReductionTower T d ⟶
      (completedReductionModuleTowerFunctor T d).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  complexCounit _ _ (completedReductionTowerCounit d T)

private def pullbackCounitNT {S T : Scheme.{u}} (f : S ⟶ T) :
    DerivedCategory.Q ⋙ completedTowerPullback f d ⟶
      (completedTowerModulePullback f d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  complexCounit _ _ (completedTowerPullbackCounit f d)

private def finiteReductionCounitNT (T : Scheme.{u}) (n : ℕ) :
    DerivedCategory.Q ⋙ cbcFiniteReduction d T n ⟶
      (cbcFiniteReductionModule d T n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  composeCounits (reductionChange T (pbcAdicProjection T d n))
    (pbcRestrict (pbcLevelConstantComparison T d n).hom)
    (reductionDerivedChange T (pbcAdicProjection T d n))
    (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom)
    (complexCounit _ _ (pbcExtensionCounit (pbcAdicProjection T d n)))
    (pbcRestrict (pbcLevelConstantComparison T d n).hom).mapDerivedCategoryFactors.hom

private theorem reductionCounitNT_iso (T : Scheme.{u})
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) P) :
    IsIso ((reductionCounitNT d T).app P) := by
  have h : IsIso ((completedReductionTowerCounit d T).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    with_unfolding_all exact (completedReductionTower_properties T d).2.2 P hP
  have := completedReductionModuleTowerFunctor_additive T d
  exact complexCounit_app_isIso (completedReductionModuleTowerFunctor T d) _ _ P h

private theorem pullbackCounitNT_iso {S T : Scheme.{u}} (f : S ⟶ T)
    (P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) :
    IsIso ((pullbackCounitNT d f).app P) := by
  have := towerPullback_counit_iso d f
  exact complexCounit_app_isIso _ _ _ P (by infer_instance)

private theorem finiteReductionCounitNT_iso (T : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) P) :
    IsIso ((finiteReductionCounitNT d T n).app P) := by
  unfold finiteReductionCounitNT
  apply composeCounits_app_isIso
  · exact complexCounit_app_isIso _ _ _ P
      (pbcExtensionCounit_isIso (pbcAdicProjection T d n) P hP)
  · infer_instance

private theorem kflat_resolutions (T : Scheme.{u})
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ∃ (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (s : P ⟶ K),
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) P ∧
        QuasiIso s := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := pbcAdicCompletion T d) K
  exact ⟨P, s, hP, hs⟩

attribute [local irreducible] finiteReductionCounitNT reductionCounitNT pullbackCounitNT
  cbcSourceModelMap cbcTargetModelMap
  cbcFiniteSourceModelMap cbcFiniteTargetModelMap cbcFiniteReductionModelMap cbcReductionModelMap

/-- Existence of the normalized finite source and target comparisons. -/
theorem cbcNormalizedFiniteComparison_exists (n : ℕ) :
    (∃ e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
          completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory,
      CbcSourceFiniteNormalization d sq n e) ∧
    (∃ e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
          cbcStrictOpen d j' sq.isOpenImmersion' ⋙
            pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory,
      CbcTargetFiniteNormalization d sq n e) := by
  have := cbcStrictOpenModule_additive d j sq.isOpenImmersion
  have := cbcStrictOpenModule_additive d j' sq.isOpenImmersion'
  have := completedTowerModulePullback_additive g d
  have := completedTowerModulePullback_additive gU d
  have := completedReductionModuleTowerFunctor_additive U d
  have := cbcFiniteSource_additive d sq n
  have := cbcFiniteTarget_additive d sq n
  have := cbcFiniteReductionModule_additive d U n
  have := cbcFiniteSourceModel_preservesZeroMorphisms d sq n
  have := cbcFiniteTargetModel_preservesZeroMorphisms d sq n
  constructor
  · have h := descentFourComparison
      (completedReductionModuleTowerFunctor U d)
      (cbcStrictOpenModule d j sq.isOpenImmersion) (completedTowerModulePullback g d)
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj (op n))
      (completedReductionTower U d) (cbcStrictOpen d j sq.isOpenImmersion)
      (completedTowerPullback g d) (pbcTowerEvaluation X' (pbcAdicCompletion X' d) n)
      (reductionCounitNT d U)
      (cbcStrictOpenModule d j sq.isOpenImmersion).mapDerivedCategoryFactors.hom
      (pullbackCounitNT d g)
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
        (op n)).mapDerivedCategoryFactors.hom
      (cbcFiniteReductionModule d U n) (cbcFiniteSource d sq n) (cbcSourceLevel d sq n)
      (cbcFiniteReduction d U n) (cbcFiniteSource d sq n).mapDerivedCategory
      (finiteReductionCounitNT d U n) (cbcFiniteSource d sq n).mapDerivedCategoryFactors.hom
      (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P)
      (kflat_resolutions d U)
      (fun P hP ↦ reductionCounitNT_iso d U P hP)
      (fun _ _ ↦ inferInstance) (fun _ _ ↦ pullbackCounitNT_iso d g _)
      (fun _ _ ↦ inferInstance) (fun P hP ↦ finiteReductionCounitNT_iso d U n P hP)
      (fun _ _ ↦ inferInstance)
    with_unfolding_all exact h
  · have h := descentFourComparison
      (completedReductionModuleTowerFunctor U d)
      (completedTowerModulePullback gU d) (cbcStrictOpenModule d j' sq.isOpenImmersion')
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj (op n))
      (completedReductionTower U d) (completedTowerPullback gU d)
      (cbcStrictOpen d j' sq.isOpenImmersion')
      (pbcTowerEvaluation X' (pbcAdicCompletion X' d) n)
      (reductionCounitNT d U) (pullbackCounitNT d gU)
      (cbcStrictOpenModule d j' sq.isOpenImmersion').mapDerivedCategoryFactors.hom
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
        (op n)).mapDerivedCategoryFactors.hom
      (cbcFiniteReductionModule d U n) (cbcFiniteTarget d sq n) (cbcTargetLevel d sq n)
      (cbcFiniteReduction d U n) (cbcFiniteTarget d sq n).mapDerivedCategory
      (finiteReductionCounitNT d U n) (cbcFiniteTarget d sq n).mapDerivedCategoryFactors.hom
      (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P)
      (kflat_resolutions d U)
      (fun P hP ↦ reductionCounitNT_iso d U P hP)
      (fun _ _ ↦ pullbackCounitNT_iso d gU _) (fun _ _ ↦ inferInstance)
      (fun _ _ ↦ inferInstance) (fun P hP ↦ finiteReductionCounitNT_iso d U n P hP)
      (fun _ _ ↦ inferInstance)
    with_unfolding_all exact h

end AlgebraicGeometry.Scheme
