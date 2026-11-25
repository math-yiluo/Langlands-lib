/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Fin.Tuple.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportSheaves
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.CategoryTheory.Integral.IntegralConstantModelLocalResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelsCommonStratification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelStrataGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Integral.IntegralHeartLocalDualityDescent
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification

/-!
# Integral stratum filtrations and the global derived Hom formula

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext,
sk-lem-int-ext-formula.md and its proof, clauses (1)--(2)
(blueprint: lemma-sections-support-closed-subscheme--3).

The coefficients, constructibility, ordinary relative derived tensor and internal Hom
are the recorded constructions. Global sections are Hom from the regular module,
as in the ringed-site hypercohomology definition, here in the module-object encoding.
The inverse-limit clause uses strict towers of complexes and the recorded Roos triangle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
open ZeroObject

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp lowerStarComp
  openImmersionLowerShriek

private theorem mapDerivedLimitTriangle
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (K : ℕ → C) [HasProduct K] [HasProduct (fun n ↦ F.obj (K n))]
    [PreservesLimit (Discrete.functor K) F]
    (f : ∀ n, K (n + 1) ⟶ K n) (A : C) (p : A ⟶ ∏ᶜ K)
    (δ : ∏ᶜ K ⟶ A⟦(1 : ℤ)⟧) (h : IsDerivedLimitTriangle f A p δ) :
    ∃ ε : (∏ᶜ fun n ↦ F.obj (K n)) ⟶ (F.obj A) ⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (fun n ↦ F.map (f n)) (F.obj A)
        (Pi.lift (fun n ↦ F.map (p ≫ Pi.π K n))) ε := by
  let e := PreservesProduct.iso F K
  let ε := e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app A
  refine ⟨ε, ?_⟩
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n ↦ F.obj (K n)) n =
      F.map (Pi.π K n) := piComparison_comp_π F K n
  have hp : F.map p ≫ e.hom = Pi.lift (fun n ↦ F.map (p ≫ Pi.π K n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← F.map_comp, Pi.lift_comp_π]
  have ht : F.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ F.map (f n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← F.map_comp]
    rw [(towerTransitionEndomorphism_eq_iff f _).mp rfl n, F.map_sub, F.map_comp]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.comp_id, Category.assoc, Pi.lift_comp_π]
    simp only [← Category.assoc, he]
  change Triangle.mk _ _ ε ∈ distinguishedTriangles
  let t := Triangle.mk p (towerTransitionEndomorphism f) δ
  let t' := Triangle.mk (Pi.lift (fun n ↦ F.map (p ≫ Pi.π K n)))
    (towerTransitionEndomorphism (fun n ↦ F.map (f n))) ε
  have et : F.mapTriangle.obj t ≅ t' :=
    Triangle.isoMk _ _ (Iso.refl _) e e
      (by simpa only [t, t', Functor.mapTriangle, Triangle.mk_mor₁,
          Iso.refl_hom, Category.id_comp] using hp)
      (by exact ht)
      (by
        change (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app A) ≫
          (shiftFunctor D (1 : ℤ)).map (𝟙 (F.obj A)) = e.hom ≫ ε
        simp [ε])
  exact isomorphic_distinguished _ (F.map_distinguished t h) _ et.symm

private theorem shortExact_dualizable_tor {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [HasDerivedCategory.{v} A]
    [Abelian.HasFunctorialFlatResolution A]
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    IsDualizable ((DerivedCategory.singleFunctor A 0).obj S.X₃) ∧
    DerivedCategory.torAmplitudeIn A (-1) 0
      ((DerivedCategory.singleFunctor A 0).obj S.X₃) := by
  refine ⟨DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hS h₁ h₂, ?_⟩
  let S' := S.map (HomologicalComplex.single A (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  let e := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app S.X₃).symm
  exact (DerivedCategory.torAmplitudeIn A (-1) 0).prop_of_iso e
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ (-1) 0
      (fun n ↦ (DerivedCategory.isDualizable_mappingCone_single_X h₁ h₂ S'.f n).flat))

private theorem shortExact_dualizable_tor_of_iso
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    {T : ShortComplex A} (hT : T.ShortExact)
    (h₁ : IsDualizable T.X₁) (h₂ : IsDualizable T.X₂)
    {M : A} (e : T.X₃ ≅ M) :
    IsDualizable ((DerivedCategory.singleFunctor A 0).obj M) ∧
      DerivedCategory.torAmplitudeIn A (-1) 0
        ((DerivedCategory.singleFunctor A 0).obj M) := by
  have h := shortExact_dualizable_tor hT h₁ h₂
  let e' := (DerivedCategory.singleFunctor A 0).mapIso e
  exact ⟨h.1.of_iso e', (DerivedCategory.torAmplitudeIn A (-1) 0).prop_of_iso e' h.2⟩

private theorem complexTensor_preservesColimits
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    (P : CochainComplex A ℤ) :
    PreservesColimitsOfSize.{v, v} ((curriedTensor (CochainComplex A ℤ)).obj P) := by
  exact (CochainComplex.tensorHomAdjunction P).leftAdjoint_preservesColimits

private theorem tensorKFlatModel
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    (D : DerivedCategory A) :
    ∃ P : CochainComplex.KFlat A,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ D) ∧
      Nonempty (DerivedCategory.Q ⋙ (curriedTensor (DerivedCategory A)).obj D ≅
        (curriedTensor (CochainComplex A ℤ)).obj P.obj ⋙ DerivedCategory.Q) := by
  classical
  let Aflat := DerivedCategory.TensorCommShift₂.LKFlat A
  have : Aflat.EssSurj := Localization.essSurj Aflat
    (HomologicalComplex.quasiIso A (.up ℤ)).WKFlat
  have hP : ∃ P : CochainComplex.KFlat A, Nonempty (Aflat.obj P ≅ D) :=
    ⟨Aflat.objPreimage D, ⟨Aflat.objObjPreimageIso D⟩⟩
  obtain ⟨P, ⟨e⟩⟩ := hP
  let q := DerivedCategory.quotientCompQhIso A
  let t := (asIso (DerivedCategory.TensorCommShift₂.liftingIsoHom A)).app P
  refine ⟨P, ⟨(q.app P.obj).symm ≪≫ e⟩, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight q.symm ((curriedTensor (DerivedCategory A)).obj D) ≪≫
    Functor.isoWhiskerLeft
      (HomotopyCategory.quotient A (.up ℤ) ⋙ DerivedCategory.Qh)
      ((curriedTensor (DerivedCategory A)).mapIso e.symm) ≪≫ t ≪≫
    Functor.isoWhiskerLeft ((curriedTensor (CochainComplex A ℤ)).obj P.obj) q

private abbrev rootMonoidal
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :
    MonoidalCategory (DerivedCategory C) := inferInstance

private abbrev rootDualizable
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) := IsDualizable K

private theorem rootDualizable_of_iso
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (K L : DerivedCategory C) (e : K ≅ L) (h : rootDualizable K) :
    rootDualizable L := h.of_iso e

private abbrev rootComplexMonoidal
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :
    MonoidalCategory (CochainComplex C ℤ) := inferInstance

private abbrev rootComplexTensor
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :=
  curriedTensor (CochainComplex C ℤ)

private theorem pairTensorLimits
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (D K : C) [ExactPairing D K] :
    PreservesLimitsOfSize.{w, w'} (tensorLeft D) :=
  (tensorLeftAdjunction D K).rightAdjoint_preservesLimits

private abbrev rootTensor
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (D : DerivedCategory C) := tensorLeft D

private abbrev rootUnit
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :
    DerivedCategory C := 𝟙_ (DerivedCategory C)

private theorem dualConsequences
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (K D : DerivedCategory C)
    (H F : DerivedCategory C ⥤ DerivedCategory C)
    (TC : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (eTC : TC = rootComplexTensor (C := C))
    (adjH : rootTensor K ⊣ H) (eF : F = rootTensor D)
    (eD : D ≅ H.obj (rootUnit (C := C)))
    (hdual : IsDualizable K)
    (hK : DerivedCategory.torAmplitudeIn C (-1) 0 K) :
    DerivedCategory.torAmplitudeIn C 0 1 D ∧ Nonempty (H ≅ F) ∧
    (∃ P : CochainComplex.KFlat C,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ D) ∧
      Nonempty (DerivedCategory.Q ⋙ F ≅
        TC.obj P.obj ⋙ DerivedCategory.Q) ∧
      ∀ (I : Type v) [SmallCategory I] [IsFiltered I],
        PreservesColimitsOfShape I (TC.obj P.obj)) ∧
    (∀ (B : ℕᵒᵖ ⥤ CochainComplex C ℤ)
      [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))]
      [HasProduct (fun n : ℕ ↦ F.obj (DerivedCategory.Q.obj (B.obj (op n))))]
      (A : DerivedCategory C)
      (p : A ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))))
      (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))) ⟶ A⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)) A p δ →
      ∃ ε : (∏ᶜ (fun n : ℕ ↦ F.obj (DerivedCategory.Q.obj (B.obj (op n))))) ⟶
          (F.obj A) ⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ F.map
            (DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)))
          (F.obj A) (Pi.lift (fun n : ℕ ↦ F.map
            (p ≫ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))) n))) ε) := by
  subst TC
  subst F
  obtain ⟨d⟩ := hdual
  let := d
  obtain ⟨braid⟩ := DerivedCategory.nonempty_braidedCategory C
  let := braid
  let D₀ := Kᘁ
  let := BraidedCategory.exactPairing_swap K D₀
  let eh : H ≅ tensorLeft D₀ := adjH.rightAdjointUniq (tensorLeftAdjunction D₀ K)
  let ed : D ≅ D₀ := eD ≪≫ eh.app _ ≪≫ ρ_ D₀
  let pairD : ExactPairing D K := exactPairingCongrLeft ed
  let F := tensorLeft D
  let := pairD
  have hD₀ : DerivedCategory.torAmplitudeIn C 0 1 D₀ :=
    DerivedCategory.torAmplitudeIn_of_exactPairing hK
  have hD := (DerivedCategory.torAmplitudeIn C 0 1).prop_of_iso ed.symm hD₀
  have : PreservesLimitsOfSize.{0, 0} F := pairTensorLimits D K
  obtain ⟨P, eP, eT⟩ := tensorKFlatModel D
  have hPcolim (I : Type v) [SmallCategory I] [IsFiltered I] :
      PreservesColimitsOfShape I ((curriedTensor (CochainComplex C ℤ)).obj P.obj) := by
    have := complexTensor_preservesColimits P.obj
    infer_instance
  refine ⟨hD, ⟨eh ≪≫ (curriedTensor _).mapIso ed.symm⟩,
    ⟨P, eP, eT, hPcolim⟩, ?_⟩
  intro B _ _ A p δ h
  exact mapDerivedLimitTriangle F
    (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))
    (fun n ↦ DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)) A p δ h

/-- Derived global sections for modules over a condensed coefficient ring.
Source: blueprint lemma-sections-support-closed-subscheme--3, global-sections convention
(blueprint: lemma-sections-support-closed-subscheme--3). -/
abbrev stratumModuleDerivedSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (X : Scheme.{u}) :=
  (preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ X))) :
    supportModules Λ X ⥤ Ab.{u + 1}).rightDerivedFunctor

/-- The uncompleted derived dual, with the coefficient ring kept abstract.
Source: blueprint lemma-sections-support-closed-subscheme--3, clause (2)
(blueprint: lemma-sections-support-closed-subscheme--3). -/
def stratumModuleDual
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (L : supportModules Λ S) :=
  ((derivedHom Λ S).obj (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj
    (𝟙_ (DerivedCategory (supportModules Λ S)))

/-- Tensor by the uncompleted derived dual over an abstract coefficient ring.
Source: blueprint lemma-sections-support-closed-subscheme--3, clause (2)
(blueprint: lemma-sections-support-closed-subscheme--3). -/
def stratumModuleDualTensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (L : supportModules Λ S) :=
  (derivedTensor Λ S).obj (stratumModuleDual Λ S L)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Full derived sections, computed by the canonical K-injective replacement, before
applying any homology functor. Source: blueprint lemma-sections-support-closed-subscheme--3, opening
convention; Stacks Project, Section 07A5 (blueprint: lemma-sections-support-closed-subscheme--3). -/
def integralStratumDerivedSections (X : Scheme.{u}) :
    integralDerived l E X ⥤ DerivedCategory Ab.{u + 1} :=
  stratumModuleDerivedSections (integralCoefficientRing l E) X

/-- Tensoring by the recorded derived dual, using the existing uncompleted relative tensor.
Source: blueprint lemma-sections-support-closed-subscheme--3, clause (2)
(blueprint: lemma-sections-support-closed-subscheme--3). -/
def integralStratumDualTensor (S : Scheme.{u})
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S) :
    integralDerived l E S ⥤ integralDerived l E S :=
  stratumModuleDualTensor (integralCoefficientRing l E) S L

private theorem monoidalRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    (inferInstance : MonoidalCategory (DerivedCategory (supportModules Λ S))) =
      rootMonoidal (C := supportModules Λ S) := rfl

private theorem tensorRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (D : DerivedCategory (supportModules Λ S)) :
    (derivedTensor Λ S).obj D = rootTensor D := by
  exact congrArg
    (fun M ↦ @tensorLeft (DerivedCategory (supportModules Λ S)) inferInstance M D)
    (monoidalRootEq Λ S)

private theorem unitRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    (𝟙_ (DerivedCategory (supportModules Λ S))) = rootUnit (C := supportModules Λ S) := by
  exact congrArg
    (fun M : MonoidalCategory (DerivedCategory (supportModules Λ S)) ↦
      @MonoidalCategoryStruct.tensorUnit (DerivedCategory (supportModules Λ S))
        inferInstance M.toMonoidalCategoryStruct)
    (monoidalRootEq Λ S)

private theorem dualizableRootOfSource
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (K : DerivedCategory (supportModules Λ S))
    (h : IsDualizable K) : rootDualizable K := by
  exact Eq.mp (congrArg
    (fun M : MonoidalCategory (DerivedCategory (supportModules Λ S)) ↦
      @IsDualizable (DerivedCategory (supportModules Λ S)) inferInstance M K)
    (monoidalRootEq Λ S)) h

private theorem dualizableRootTransport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (K : DerivedCategory (supportModules Λ S))
    (h : rootDualizable K) : IsDualizable K := by
  exact Eq.mpr (congrArg
    (fun M : MonoidalCategory (DerivedCategory (supportModules Λ S)) ↦
      @IsDualizable (DerivedCategory (supportModules Λ S)) inferInstance M K)
    (monoidalRootEq Λ S)) h

-- The same comparison keeps tensor totalization abstract in the K-flat model clause.

private theorem complexMonoidalRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    (inferInstance : MonoidalCategory (CochainComplex (supportModules Λ S) ℤ)) =
      rootComplexMonoidal (C := supportModules Λ S) := rfl

private theorem complexTensorRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    curriedTensor (CochainComplex (supportModules Λ S) ℤ) =
      rootComplexTensor (C := supportModules Λ S) := by
  exact congrArg
    (fun M : MonoidalCategory (CochainComplex (supportModules Λ S) ℤ) ↦
      @curriedTensor (CochainComplex (supportModules Λ S) ℤ) inferInstance M)
    (complexMonoidalRootEq Λ S)

-- The preceding equations expose the needed comparisons without expanding chosen functors.

end AlgebraicGeometry.ProEtale.CondensedRing
