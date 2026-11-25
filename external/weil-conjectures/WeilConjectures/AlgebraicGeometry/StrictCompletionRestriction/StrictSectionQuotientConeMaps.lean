/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import all WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictIntegralCompletionPresentation
import all WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionScalarPresentation
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Section principal cones map to actual quotient tensors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance 2000] sheafMonoidalCategory sheafBraidedCategory

section TensorComparison
universe c v w
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, c}] [HasSheafify J AddCommGrpCat.{c}]
  [(J.W (A := AddCommGrpCat.{c})).IsMonoidal]
  (R : Sheaf J AddCommGrpCat.{c}) [MonObj R] [IsCommMonObj R]
  (N : Mod (Sheaf J AddCommGrpCat.{c}) R)
  (Q : SheafOfModules.{c}
    ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj (sectionRingSheaf J R)))
  (e : (sectionModuleEquivalence J R).functor.obj N ≅ Q)

private def sectionTensorIso (M : Mod (Sheaf J AddCommGrpCat.{c}) R) :
    (sectionModuleEquivalence J R).functor.obj (M ⊗ N) ≅
      (SheafOfModules.siteSheafTensorRight.{w, v, c, c} Q).obj
        ((sectionModuleEquivalence J R).functor.obj M) := by
  let F := (sectionModuleEquivalence J R).functor
  let S := PresheafOfModules.sheafification.{c} (J := J) (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj (sectionRingSheaf J R)).obj)
  exact (exists_sectionTensorIso J R M N).choose ≪≫
    S.mapIso (((tensorLeft (F.obj M).val).mapIso
      ((SheafOfModules.forget _).mapIso e)) ≪≫
      ((SheafOfModules.siteTensorRightIso.{v, w, c} (sectionRingSheaf J R) Q.val).app
        (F.obj M).val).symm)

private theorem sectionTensorIso_tmul (M : Mod (Sheaf J AddCommGrpCat.{c}) R)
    (U : Cᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    (sectionTensorIso J R N Q e M).hom.val.app U
      (comparison_internalTmul J R M N U x y) =
      SheafOfModules.siteSheafTensorTmul.{v, w, c, c}
        ((sectionModuleEquivalence J R).functor.obj M) Q U x (e.hom.val.app U y) := by
  let F := (sectionModuleEquivalence J R).functor
  let adj := PresheafOfModules.sheafificationAdjunction.{c} (J := J) (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj (sectionRingSheaf J R)).obj)
  let g := ((tensorLeft (F.obj M).val).mapIso
    ((SheafOfModules.forget _).mapIso e)).hom ≫
    ((SheafOfModules.siteTensorRightIso.{v, w, c} (sectionRingSheaf J R) Q.val).app
      (F.obj M).val).inv
  change ((PresheafOfModules.sheafification.{c} (J := J) (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj
        (sectionRingSheaf J R)).obj)).map g).val.app U
      (((exists_sectionTensorIso J R M N).choose).hom.val.app U
        (comparison_internalTmul J R M N U x y)) = _
  erw [(exists_sectionTensorIso J R M N).choose_spec U x y]
  exact (congrArg (fun f ↦ f.app U (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y))
    (adj.unit.naturality g)).symm

attribute [local irreducible] sectionTensorIso

private theorem sectionTensorIso_natural
    {M M' : Mod (Sheaf J AddCommGrpCat.{c}) R} (f : M ⟶ M') :
    (sectionModuleEquivalence J R).functor.map (f ▷ N) ≫
        (sectionTensorIso J R N Q e M').hom =
      (sectionTensorIso J R N Q e M).hom ≫
        (SheafOfModules.siteSheafTensorRight.{w, v, c, c} Q).map
          ((sectionModuleEquivalence J R).functor.map f) := by
  let F := (sectionModuleEquivalence J R).functor
  apply comparison_internalTensor_hom_ext J R M N
  intro U x y
  change (sectionTensorIso J R N Q e M').hom.val.app U
    ((F.map (f ▷ N)).val.app U (comparison_internalTmul J R M N U x y)) = _
  rw [← tensorHom_id]
  erw [comparison_internalTmul_natural J R f (𝟙 _) U x y]
  rw [sectionTensorIso_tmul]
  dsimp only [Functor.map_id]
  change _ = ((SheafOfModules.siteSheafTensorRight.{w, v, c, c} Q).map _).val.app U
    ((sectionTensorIso J R N Q e M).hom.val.app U
      (comparison_internalTmul J R M N U x y))
  rw [sectionTensorIso_tmul]
  let adj := PresheafOfModules.sheafificationAdjunction.{c} (J := J) (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{c} RingCat.{c})).obj (sectionRingSheaf J R)).obj)
  exact congrArg (fun h ↦ h.app U
    ((show (F.obj M).val.obj U from x) ⊗ₜ[(sectionRingSheaf J R).obj.obj U]
      (e.hom.val.app U y)))
    (adj.unit.naturality (SheafOfModules.siteTensorHom (F.map f).val Q.val))

private theorem sectionTensorIso_unit_apply (p : 𝟙_ (Mod (Sheaf J AddCommGrpCat.{c}) R) ⟶ N)
    (M : Mod (Sheaf J AddCommGrpCat.{c}) R) (U : Cᵒᵖ) (x : M.X.obj.obj U) :
    ((sectionModuleEquivalence J R).functor.map ((ρ_ M).inv ≫ M ◁ p) ≫
      (sectionTensorIso J R N Q e M).hom).val.app U x =
      SheafOfModules.siteSheafTensorTmul.{v, w, c, c}
        ((sectionModuleEquivalence J R).functor.obj M) Q U x
        (e.hom.val.app U (((sectionModuleEquivalence J R).functor.map p).val.app U
          (1 : (sectionRingSheaf J R).obj.obj U))) := by
  let F := (sectionModuleEquivalence J R).functor
  have hi : (F.map (ρ_ M).inv).val.app U x =
      comparison_internalTmul J R M (𝟙_ _) U x
        (1 : (sectionRingSheaf J R).obj.obj U) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ U).map (F.map (ρ_ M).hom))).1
    have hh := congrArg (fun f ↦ f.val.app U x) (F.mapIso (ρ_ M)).inv_hom_id
    change (F.map (ρ_ M).hom).val.app U ((F.map (ρ_ M).inv).val.app U x) = _
    erw [comparison_internalTmul_rightUnitor J R M U x
      (1 : (sectionRingSheaf J R).obj.obj U)]
    rw [one_smul]
    exact hh
  change (sectionTensorIso J R N Q e M).hom.val.app U
    ((F.map (M ◁ p)).val.app U ((F.map (ρ_ M).inv).val.app U x)) = _
  rw [hi, ← id_tensorHom]
  erw [comparison_internalTmul_natural J R (𝟙 M) p]
  rw [sectionTensorIso_tmul]
  rfl
private def sectionTensorComplexIso
    (K : CochainComplex (Mod (Sheaf J AddCommGrpCat.{c}) R) ℤ) :
    ((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj
        (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((SheafOfModules.siteSheafTensorRight.{w, v, c, c} Q).mapHomologicalComplex
        (.up ℤ)).obj
        (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ sectionTensorIso J R N Q e (K.X q))
    (fun q q' _ ↦ (sectionTensorIso_natural J R N Q e (K.d q q')).symm)

private theorem sectionTensorComplexIso_hom_f
    (K : CochainComplex (Mod (Sheaf J AddCommGrpCat.{c}) R) ℤ) (q : ℤ) :
    (sectionTensorComplexIso J R N Q e K).hom.f q =
      (sectionTensorIso J R N Q e (K.X q)).hom := rfl

attribute [local irreducible] sectionTensorComplexIso

end TensorComparison

private theorem sectionKflat
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : CochainComplex (Internal Λ X) ℤ) (P : CochainComplex (Modules Λ X) ℤ)
    (e : ((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj K ≅ P)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ X) P) :
    (HomologicalComplex.quasiIso (Internal Λ X) (.up ℤ)).kFlat K := by
  have hKP : CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ X)
      (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj K) := by
    intro A hA
    let t := ((curriedTensor _).map₂CochainComplex.obj A).mapIso e
    exact fun q ↦ ((hP A hA) q).of_iso t.symm
  have hK' := (comparison_kflat (Scheme.ProEt.topology X) (condensedRingObj Λ X) K).mpr hKP
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro A hA
  obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hA
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor A K (curriedTensor _))).2 (hK' A hA)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

private def finiteSectionIso (X : Scheme.{u}) (n : ℕ) :
    (equivalence (DerivedNakayama.integerRing l E) X).functor.obj
        (AdicCompletion.finiteModule l E X n) ≅
      SheafOfModules.KFlatRoos.algebraModule.{u + 1, u, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.quotient l E X n)) :=
  (equivalence (DerivedNakayama.integerRing l E) X).functor.mapIso
      (AdicCompletion.finiteModuleIso l E X n) ≪≫
    (CondensedRing.sectionModuleComapIso X (AdicCompletion.quotient l E X n)).app
      (Mod.regular (AdicCompletion.finiteRing l E X n)) ≪≫
    (SheafOfModules.restrictScalars _).mapIso
      (CondensedRing.sectionModuleRegularIso X (AdicCompletion.finiteRing l E X n))

private theorem finiteSectionIso_unit (X : Scheme.{u}) (n : ℕ) (U : X.ProEtᵒᵖ) :
    ((finiteSectionIso l E X n).hom.val.app U)
      (((equivalence (DerivedNakayama.integerRing l E) X).functor.map
        (AdicCompletion.finiteUnit l E X n)).val.app U
          (1 : (ring (DerivedNakayama.integerRing l E) X).obj.obj U)) =
      (1 : (sectionRingSheaf (Scheme.ProEt.topology X)
        (AdicCompletion.finiteRing l E X n)).obj.obj U) := by
  change (AdicCompletion.quotient l E X n).hom.app U
    (1 : (ring (DerivedNakayama.integerRing l E) X).obj.obj U) = _
  exact map_one ((sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (AdicCompletion.quotient l E X n)).hom.app U).hom

attribute [local irreducible] finiteSectionIso

section Transport
universe a b v w
variable {A : Type a} {D : Type b} [Category.{v} A] [Category.{w} D]
  [Abelian A] [Abelian D] [HasDerivedCategory.{w} D]

omit [HasDerivedCategory D] in
private theorem square_zero (F : A ⥤ D) [F.PreservesZeroMorphisms]
    {K L : A} {P Q : D} (f : K ⟶ K) (η : K ⟶ L) (hz : f ≫ η = 0)
    (i : F.obj K ≅ P) (j : F.obj L ≅ Q) (g : P ⟶ P) (ρ : P ⟶ Q)
    (hf : F.map f ≫ i.hom = i.hom ≫ g)
    (hη : F.map η ≫ j.hom = i.hom ≫ ρ) : g ≫ ρ = 0 := by
  apply (cancel_epi i.hom).mp
  calc
    i.hom ≫ g ≫ ρ = F.map f ≫ i.hom ≫ ρ :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h ↦ h ≫ ρ) hf.symm).trans (Category.assoc _ _ _))
    _ = F.map f ≫ F.map η ≫ j.hom := congrArg (fun h ↦ F.map f ≫ h) hη.symm
    _ = 0 := by rw [← Functor.map_comp_assoc, hz, F.map_zero, zero_comp]
    _ = i.hom ≫ 0 := (comp_zero).symm

omit [HasDerivedCategory D] in
private theorem coneMap_quasiIso {K P : CochainComplex D ℤ} (f : K ⟶ K) (g : P ⟶ P)
    (i : K ≅ P) (h : f ≫ i.hom = i.hom ≫ g) :
    QuasiIso (CochainComplex.mappingCone.map f g i.hom i.hom h) := by
  have hi : g ≫ i.inv = i.inv ≫ f := by
    apply (cancel_mono i.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  let e : CochainComplex.mappingCone f ≅ CochainComplex.mappingCone g :=
    { hom := CochainComplex.mappingCone.map f g i.hom i.hom h
      inv := CochainComplex.mappingCone.map g f i.inv i.inv hi
      hom_inv_id := by
        rw [← CochainComplex.mappingCone.map_comp]
        simp only [Iso.hom_inv_id, CochainComplex.mappingCone.map_id]
      inv_hom_id := by
        rw [← CochainComplex.mappingCone.map_comp]
        simp only [Iso.inv_hom_id, CochainComplex.mappingCone.map_id] }
  have : IsIso (CochainComplex.mappingCone.map f g i.hom i.hom h) := e.isIso_hom
  infer_instance

omit [HasDerivedCategory D] in
private theorem desc_quasiIso_transport (F : A ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : CochainComplex A ℤ} (f : K ⟶ K) (η : K ⟶ L) (hz : f ≫ η = 0)
    (hd : QuasiIso (CochainComplex.mappingCone.descShortComplex (ShortComplex.mk f η hz)))
    {P Q : CochainComplex D ℤ}
    (i : (F.mapHomologicalComplex (.up ℤ)).obj K ≅ P)
    (j : (F.mapHomologicalComplex (.up ℤ)).obj L ≅ Q)
    (g : P ⟶ P) (ρ : P ⟶ Q)
    (hf : (F.mapHomologicalComplex (.up ℤ)).map f ≫ i.hom = i.hom ≫ g)
    (hη : (F.mapHomologicalComplex (.up ℤ)).map η ≫ j.hom = i.hom ≫ ρ)
    (hw : g ≫ ρ = 0) :
    QuasiIso (CochainComplex.mappingCone.descShortComplex (ShortComplex.mk g ρ hw)) := by
  have := hd
  let S := ShortComplex.mk f η hz
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let b := CochainComplex.mappingCone.descShortComplex (S.map Fc)
  have : QuasiIso (Fc.map (CochainComplex.mappingCone.descShortComplex S)) := by
    infer_instance
  have hb : QuasiIso b := by
    have hh := CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex F S
    have he : QuasiIso
        ((CochainComplex.mappingCone.mapHomologicalComplexIso f F).hom ≫ b) := by
      rw [hh]
      infer_instance
    exact (quasiIso_iff_comp_left _ _).mp he
  let m := CochainComplex.mappingCone.map (Fc.map f) g i.hom i.hom hf
  have hm : QuasiIso m := coneMap_quasiIso _ _ i hf
  have he : m ≫ CochainComplex.mappingCone.descShortComplex
      (ShortComplex.mk g ρ hw) = b ≫ j.hom := by
    exact CochainComplex.mappingCone.map_descShortComplex (S.map Fc)
      (ShortComplex.mk g ρ hw)
      (ShortComplex.homMk i.hom i.hom j.hom hf.symm hη.symm)
  have : QuasiIso (m ≫ CochainComplex.mappingCone.descShortComplex
      (ShortComplex.mk g ρ hw)) := by
    rw [he]
    infer_instance
  exact (quasiIso_iff_comp_left m _).mp this
end Transport

private theorem presentationConeMap {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] [HasDerivedCategory A] (T : Presentation A)
    (P : CochainComplex A ℤ) (n : ℕ) (Q : CochainComplex A ℤ) (ρ : P ⟶ Q)
    (hw : (NatTrans.mapHomologicalComplex (T.scalar ^ (n + 1)).asHom (.up ℤ)).app P ≫ ρ = 0)
    (hc : QuasiIso (CochainComplex.mappingCone.descShortComplex
      (ShortComplex.mk _ ρ hw))) :
    ∃ c : (T.tower.obj P).asFunctor.obj (op n) ⟶ Q,
      QuasiIso c ∧ ∀ q : ℤ,
        c.f q = (T.coordinates P n q).hom ≫ biprod.fst ≫ ρ.f q := by
  have := hc
  let g : P ⟶ P :=
    (NatTrans.mapHomologicalComplex (T.scalar ^ (n + 1)).asHom (.up ℤ)).app P
  let τ : CochainComplex.mappingCone g ⟶ Q :=
    CochainComplex.mappingCone.descShortComplex (ShortComplex.mk g ρ hw)
  refine ⟨(eqToIso (T.cone P n)).hom ≫ τ, inferInstance, ?_⟩
  intro q
  rw [T.coordinates_eq]
  have ht : τ.f q = (CochainComplex.mappingCone.snd g).v q q (add_zero q) ≫ ρ.f q := by
    dsimp only [τ, CochainComplex.mappingCone.descShortComplex]
    rw [CochainComplex.mappingCone.desc_f _ _ _ _ q (q + 1) rfl]
    simp only [CochainComplex.HomComplex.Cochain.zero_v, comp_zero, zero_add]
  simpa only [eqToIso_refl, Iso.refl_hom, Category.id_comp] using!
    CoefficientCone.cone_transport_coordinates (T.cone P n) (rfl : g = g) τ q (ρ.f q) ht

private theorem transportSectionCone
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1} (Modules Λ X)) (n : ℕ)
    (N : Internal Λ X) (Q : Modules Λ X)
    (eN : (equivalence Λ X).functor.obj N ≅ Q)
    (p : 𝟙_ (Internal Λ X) ⟶ N) (r : End (𝟭 (Internal Λ X)))
    (ρ₀ : 𝟭 (Modules Λ X) ⟶
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} Q :
        Modules Λ X ⥤ Modules Λ X))
    (hs : ∀ M, (equivalence Λ X).functor.map (r.asHom.app M) =
      (T.scalar ^ (n + 1)).asHom.app ((equivalence Λ X).functor.obj M))
    (hu : ∀ M, (equivalence Λ X).functor.map ((ρ_ M).inv ≫ M ◁ p) ≫
      (sectionTensorIso (Scheme.ProEt.topology X) (condensedRingObj Λ X) N Q eN M).hom =
        ρ₀.app ((equivalence Λ X).functor.obj M))
    (hcone : ∀ K : CochainComplex (Internal Λ X) ℤ,
      (HomologicalComplex.quasiIso (Internal Λ X) (.up ℤ)).kFlat K →
      ∃ hz : (NatTrans.mapHomologicalComplex r.asHom (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex
          ((rightUnitorNatIso (Internal Λ X)).inv ≫
            (tensoringRight (Internal Λ X)).map p) (.up ℤ)).app K = 0,
        QuasiIso (CochainComplex.mappingCone.descShortComplex (ShortComplex.mk _ _ hz)))
    (P : CochainComplex (Modules Λ X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ X) P) :
    ∃ c : (T.tower.obj P).asFunctor.obj (op n) ⟶
      ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} Q).mapHomologicalComplex
        (.up ℤ)).obj P,
      QuasiIso c ∧ ∀ q : ℤ,
        c.f q = (T.coordinates P n q).hom ≫ biprod.fst ≫ ρ₀.app (P.X q) := by
  let F := (equivalence Λ X).functor
  have : (F.mapHomologicalComplex (.up ℤ)).EssSurj :=
    ((equivalence Λ X).mapHomologicalComplex (.up ℤ)).essSurj_functor
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F.mapHomologicalComplex (.up ℤ)) P
  let L := (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} Q).mapHomologicalComplex
    (.up ℤ)
  let I := (tensorRight N).mapHomologicalComplex (.up ℤ)
  let j : (F.mapHomologicalComplex (.up ℤ)).obj (I.obj K) ≅ L.obj P :=
    sectionTensorComplexIso (Scheme.ProEt.topology X) (condensedRingObj Λ X) N Q eN K ≪≫
      L.mapIso e
  let f : K ⟶ K := (NatTrans.mapHomologicalComplex r.asHom (.up ℤ)).app K
  let g : P ⟶ P := (NatTrans.mapHomologicalComplex (T.scalar ^ (n + 1)).asHom (.up ℤ)).app P
  let η : K ⟶ I.obj K := (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso (Internal Λ X)).inv ≫
      (tensoringRight (Internal Λ X)).map p) (.up ℤ)).app K
  let ρ : P ⟶ L.obj P := (NatTrans.mapHomologicalComplex ρ₀ (.up ℤ)).app P
  have hf : (F.mapHomologicalComplex (.up ℤ)).map f ≫ e.hom = e.hom ≫ g := by
    apply HomologicalComplex.hom_ext
    intro q
    change F.map (r.asHom.app (K.X q)) ≫ e.hom.f q = _
    rw [hs]
    exact ((T.scalar ^ (n + 1)).asHom.naturality (e.hom.f q)).symm
  have hη : (F.mapHomologicalComplex (.up ℤ)).map η ≫ j.hom = e.hom ≫ ρ := by
    apply HomologicalComplex.hom_ext
    intro q
    simp only [j, Iso.trans_hom, HomologicalComplex.comp_f, sectionTensorComplexIso_hom_f]
    change F.map ((ρ_ (K.X q)).inv ≫ K.X q ◁ p) ≫
      (sectionTensorIso (Scheme.ProEt.topology X) (condensedRingObj Λ X)
        N Q eN (K.X q)).hom ≫ _ = _
    rw [← Category.assoc, hu]
    exact (ρ₀.naturality (e.hom.f q)).symm
  obtain ⟨hz, hd⟩ := hcone K (sectionKflat Λ X K P e hP)
  have hw := square_zero (F.mapHomologicalComplex (.up ℤ)) f η hz e j g ρ hf hη
  have hc := desc_quasiIso_transport F f η hz hd e j g ρ hf hη hw
  exact presentationConeMap T P n (L.obj P) ρ hw hc

private theorem scalarSection_pow (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1}
      (Modules (DerivedNakayama.integerRing l E) X))
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hscalar : ∀ (M : Modules (DerivedNakayama.integerRing l E) X) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U),
      (T.scalar.asHom.app M).val.app U x = sectionScalarValue l E X d U • x)
    (M : AdicCompletion.Modules l E X) (k : ℕ) :
    (equivalence (DerivedNakayama.integerRing l E) X).functor.map
      ((DerivedNakayama.scalarOnModules l E X (d ^ k)).app M) =
      (T.scalar ^ k).asHom.app
        ((equivalence (DerivedNakayama.integerRing l E) X).functor.obj M) := by
  have hb (N : AdicCompletion.Modules l E X) :
      (equivalence (DerivedNakayama.integerRing l E) X).functor.map
        ((DerivedNakayama.scalarOnModules l E X d).app N) =
      T.scalar.asHom.app ((equivalence (DerivedNakayama.integerRing l E) X).functor.obj N) := by
    ext U x
    exact (section_scalar_value l E X d N U x).trans (hscalar _ U x).symm
  rw [scalarOnModules_pow]
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [pow_succ, End.mul_asHom, NatTrans.comp_app, Functor.map_comp, ih]
      exact congrArg (fun h ↦ h ≫ _) (hb M)

-- Instantiate the abstract transport with the actual coefficient quotient.
private theorem quotientConeMap (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1}
      (Modules (DerivedNakayama.integerRing l E) X))
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hscalar : ∀ (M : Modules (DerivedNakayama.integerRing l E) X) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U),
      (T.scalar.asHom.app M).val.app U x = sectionScalarValue l E X data.d U • x)
    (P : CochainComplex (Modules (DerivedNakayama.integerRing l E) X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := ring (DerivedNakayama.integerRing l E) X) P) (n : ℕ)
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (φ : ring (DerivedNakayama.integerRing l E) X ⟶ S)
    (hS : S = sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (AdicCompletion.finiteRing l E X n))
    (hφ : HEq φ (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (AdicCompletion.quotient l E X n))) :
    ∃ c : (T.tower.obj P).asFunctor.obj (op n) ⟶
      ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (SheafOfModules.KFlatRoos.algebraModule.{u + 1, u, u + 1} φ)).mapHomologicalComplex
          (.up ℤ)).obj P,
      QuasiIso c ∧ ∀ q : ℤ, c.f q =
        (T.coordinates P n q).hom ≫ biprod.fst ≫
          (SheafOfModules.KFlatRoos.tensorUnit.{u + 1, u, u + 1} φ).app (P.X q) := by
  subst S
  cases eq_of_heq hφ
  refine transportSectionCone (DerivedNakayama.integerRing l E) X T n
    (AdicCompletion.finiteModule l E X n) _ (finiteSectionIso l E X n)
    (AdicCompletion.finiteUnit l E X n)
    (.of (DerivedNakayama.scalarOnModules l E X (data.d ^ (n + 1))))
    (SheafOfModules.KFlatRoos.tensorUnit.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.quotient l E X n))) ?_ ?_ ?_ P hP
  · intro M
    exact scalarSection_pow l E X T data.d hscalar M (n + 1)
  · intro M
    ext U x
    have h := sectionTensorIso_unit_apply (Scheme.ProEt.topology X)
      (AdicCompletion.ring l E X) (AdicCompletion.finiteModule l E X n) _
      (finiteSectionIso l E X n) (AdicCompletion.finiteUnit l E X n) M U x
    rw [h, finiteSectionIso_unit]
    exact ((SheafOfModules.KFlatRoos.tensorUnit_existsUnique
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.quotient l E X n))).exists.choose_spec _ U x).symm
  · intro K hK
    refine ⟨CoefficientCone.coneToTensor_zero l E X data hdata K n, ?_⟩
    have hc := CoefficientCone.coneToTensor_quasiIso l E X data hdata K hK n
    exact (quasiIso_iff_comp_left (eqToIso (data.hobj n K)).hom _).mp hc

/-- The canonical principal-cone maps to the actual quotient tensors, before Roos
completion or derived localization.

Source: blueprint latest, derived-nakayama-first-reduction proof, Cones paragraph;
Locality in integral-ctf-equals-bc; Stacks 03EK, 06YS and 06YT
(blueprint: lem-sfb-strict-section-quotient-cone-maps).

Proof: use the existing internal principal-cone augmentation. The exact section
module equivalence identifies its finite coefficient module with the actual
section algebra module, using restriction of scalars and the regular-module
comparison. Sheafify the ordinary section tensor comparison and this coefficient
isomorphism. Naturality of sheafification gives its pure-tensor formula and
naturality in the input module. The right unitor and finite coefficient unit
identify its composite with the internal tensor unit as exactly tensorUnit.
Apply the inverse termwise section equivalence to P. Its counit transfers the
specified K-flatness to this internal representative by the total-tensor
comparison. Equality on local sections identifies the internal scalar with
T.scalar, including all positive powers. The existing internal cone augmentation
is a quasi-isomorphism on this K-flat representative. Cone descent commutes with
the exact section equivalence and with the counit and tensor isomorphisms, so
the section augmentation is also a quasi-isomorphism. Transport across T.cone;
the descShortComplex formula and T.coordinates_eq give the displayed components.
Finally eliminate the supplied coefficient object and morphism equalities at
each level and assemble the family.
Only positive exponents occur, so the point scalar is regular; on an empty site
or for a zero quotient the same exact sequences and coordinate formulas apply. -/
theorem strictSectionQuotientConeMaps (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1}
      (Modules (DerivedNakayama.integerRing l E) X))
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hscalar : ∀ (M : Modules (DerivedNakayama.integerRing l E) X) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U),
      (T.scalar.asHom.app M).val.app U x = sectionScalarValue l E X data.d U • x)
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (ι : (Functor.const ℕᵒᵖ).obj (ring (DerivedNakayama.integerRing l E) X) ⟶ B)
    (hB : ∀ n : ℕ, B.obj (op n) = sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.finiteRing l E X n))
    (hι : ∀ n : ℕ, HEq (ι.app (op n))
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.quotient l E X n)))
    (P : CochainComplex (Modules (DerivedNakayama.integerRing l E) X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := ring (DerivedNakayama.integerRing l E) X) P) :
    ∃ c : ∀ n : ℕ, (T.tower.obj P).asFunctor.obj (op n) ⟶
        (SheafOfModules.KFlatRoos.level.{u + 1, u, u + 1} B ι n).obj P,
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ (n : ℕ) (q : ℤ), (c n).f q =
        (T.coordinates P n q).hom ≫ biprod.fst ≫
          (SheafOfModules.KFlatRoos.tensorUnit.{u + 1, u, u + 1}
            (ι.app (op n))).app (P.X q)) := by
  classical
  choose c hc hcoord using fun n ↦ quotientConeMap l E X T data hdata hscalar P hP n
    (B.obj (op n)) (ι.app (op n)) (hB n) (hι n)
  exact ⟨c, hc, hcoord⟩

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
