/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Logic.Function.Basic
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Equivalence
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOperationsExistence
import WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictSystemGeometricRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenWordEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteWordIdentification
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityFiniteLevelProjectionTransport

set_option linter.privateModule false

/-! Finite-level comparison and conservativity for compact-support projection.

Source: paragraph (3) of
`sk-prop-sp-integral-adjunction-direct-image.proof.md`.
(blueprint: lem-sp-tower-compact-support-projection-formula)

The proof evaluates the two transposes at each finite coefficient quotient,
uses the bounded constructible finite-Tor projection theorem and the open
unit/counit triangles, then applies joint conservativity of the tower
calculus. The final mate is the recorded `projection` arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek
open SheafOfModules

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem evaluation_sections (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.obj U)
      (((spCoefficientEvaluation l E T D.equivalence n).obj M).val.obj U) := by
  dsimp [SpTowerShriek.ev, WeilConjectures.SemilinearSections.evaluation,
    SheafOfModules.pushforward,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj,
    spCoefficientEvaluation, systemEvaluation]
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app, eqToHom_refl]
  exact (b.sections T M n U).trans (D.sections M n U).symm

private theorem hom_function_heq {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {g : M' ⟶ N'} (hfg : HEq f g) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  cases hM
  cases hN
  cases hfg
  rfl

-- Comparing the two concrete ring-presheaf presentations requires unfolding their objects.
private theorem evaluation_restrictions (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.map f x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).obj M).val.map f x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.obj M).val.map
      (Prod.mkHom (𝟙 n) f.unop).op x)
    (fun x ↦ ((D.equivalence.functor.obj M).level n).val.map f x)
  have hB := b.restrictions T M (Prod.mkHom (𝟙 n) f.unop).op
  have hD := D.restrictions M n f
  refine hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm)) ?_
    (hB.trans hD.symm)
  have hmap :
      ((WeilConjectures.SemilinearSections.ring
        (WeilConjectures.coefficientSequenceTopology (ProEt.topology T))
        (WeilConjectures.SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj.map
            (Prod.mkHom (𝟙 n) f.unop).op).hom =
      ((spCoefficientRing l E T n).obj.map f).hom := by
    change ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((((WeilConjectures.SemilinearSections.rings (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (𝟙 (op n))).hom.app U) ≫
          (SpTowerShriek.B l E T n).obj.map f)).hom =
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((SpTowerShriek.B l E T n).obj.map f)).hom
    erw [CategoryTheory.Functor.map_id]
    simp
  rw [hmap]
  exact congrArg (ModuleCat.restrictScalars
    (((spCoefficientRing l E T n).obj).map f).hom).obj
    (eq_of_heq ((b.sections T M n V).trans (D.sections M n V).symm))

-- Evaluation changes scalar actions but leaves these underlying section functions intact.
private theorem evaluation_maps (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    {M N : spCoefficientTowers l E T} (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).map ((b.realization T).functor.map f)).val.app U x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.map f).val.app (op (n, U.unop)) x)
    (fun x ↦ ((D.equivalence.functor.map f).app n).val.app U x)
  exact hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm))
    (eq_of_heq ((b.sections T N n U).trans (D.sections N n U).symm))
    ((b.morphisms T f (op (n, U.unop))).trans (D.morphisms f n U).symm)

private theorem transport_restriction {A B : Type*} [Ring A] [Ring B]
    (q : A →+* B) {M M' : ModuleCat A} {N N' : ModuleCat B}
    (hM : M = M') (hN : N = N')
    (f : M ⟶ (ModuleCat.restrictScalars q).obj N)
    (g : M' ⟶ (ModuleCat.restrictScalars q).obj N')
    (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ (ModuleCat.restrictScalars q).map (eqToHom hN) = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private theorem transport_morphism {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ eqToHom hN = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private def evaluation_object (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) :
    (SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M) ≅
      (spCoefficientEvaluation l E T D.equivalence n).obj M where
  hom := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U))
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D M n V)) _ _
      (evaluation_restrictions l E b T D M n f) }⟩
  inv := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U)).symm
      (eq_of_heq (evaluation_sections l E b T D M n V)).symm _ _
      (evaluation_restrictions l E b T D M n f).symm }⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]

private def evaluation_iso (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (b.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T D.equivalence n :=
  NatIso.ofComponents (fun M ↦ evaluation_object l E b T D M n) (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change ((SpTowerShriek.ev l E T n).map
        ((b.realization T).functor.map f)).val.app U ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D N n U)) =
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
        ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U
    exact transport_morphism
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D N n U)) _ _
      (evaluation_maps l E b T D f n U))

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private def equivalence_counit_transport {A B : Type*} [Category* A] [Category* B]
    (e : A ≌ B) (F : A ⥤ B) (h : e.functor = F) (K : B) :
    F.obj (e.inverse.obj K) ≅ K := by
  cases h
  exact e.counitIso.app K

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers

attribute [local irreducible] HasProEtaleTorAmplitude ProEtale.projectionMapOfCompactification
  ProEtale.derivedTensor
  CategoryTheory.Functor.leftDerivedFunctor ProEtale.upperStar
attribute [local instance 100000] SheafOfModules.instAbelian
attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem fixed_constructible
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u})
    (K : proEtaleDerivedCategory W A)
    (hc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf W A
      ((DerivedCategory.homologyFunctor _ i).obj K))
    (a b : ℤ) (hab : a ≤ b)
    (hv : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W
      ((sfIntrinsicDerivedEquivalence W A).inverse.obj K) := by
  obtain ⟨M, ⟨eM⟩⟩ := ((finiteRing_constructibleDerived_origin W A).2.2.1 K).mpr
    ⟨hc, a, b, hab, hv⟩
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W
  let G := ProEtale.finiteCoefficientIntrinsicRealization W A
  let R := sfIntrinsicDerivedEquivalence W A
  let ecomp : ProEtale.finiteCoefficientIntrinsicDerivedComparison W A ≅
      F.mapDerivedCategory.{u + 1, u + 1} ⋙ R.functor :=
    (Functor.mapDerivedCategoryCompIso F G).symm
  let e : F.mapDerivedCategory.{u + 1, u + 1}.obj M.obj ≅ R.inverse.obj K :=
    R.unitIso.app _ ≪≫ R.inverse.mapIso
      (ecomp.symm.app M.obj ≪≫ eM)
  have hb : DerivedCategory.TStructure.t.bounded M.obj := by
    obtain ⟨r, s, _, hz⟩ := M.property.2
    exact ⟨⟨r, (DerivedCategory.isGE_iff _ r).mpr (fun i hi ↦ hz i (.inl hi))⟩,
      ⟨s, (DerivedCategory.isLE_iff _ s).mpr (fun i hi ↦ hz i (.inr hi))⟩⟩
  apply (ProEtale.DerivedCategory.boundedConstructible_iff _ _ _).mpr
  exact ⟨M.obj, ⟨hb, fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (M.property.1 i)⟩, ⟨e⟩⟩

private theorem intrinsic_derived_inverse (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).inverse =
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory := by
  unfold sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  rfl

attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem fixed_tor
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u})
    (K : proEtaleDerivedCategory W A) (a b : ℤ)
    (ht : HasProEtaleTorAmplitude W A K a b) :
    ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W a b
      ((sfIntrinsicDerivedEquivalence W A).inverse.obj K) := by
  rw [intrinsic_derived_inverse]
  let R := sfIntrinsicModuleEquivalence W A
  have hab : a ≤ b := by
    unfold HasProEtaleTorAmplitude at ht
    exact ht.1
  have ht' : HasProEtaleTorAmplitude W A
      (R.functor.mapDerivedCategory.obj (R.inverse.mapDerivedCategory.obj K)) a b := by
    unfold HasProEtaleTorAmplitude at ht ⊢
    refine ⟨ht.1, ?_⟩
    intro B P hB v hv hP M i hi
    exact ht.2 B P (hB.map (fun z ↦ z ≪≫ R.mapDerivedCategory.counitIso.app K))
      v hv hP M i hi
  have h := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A W a b hab (R.inverse.mapDerivedCategory.obj K)).mp
      (by simpa only [R, sfIntrinsicModuleEquivalence, Functor.asEquivalence_functor] using ht')
  exact h

private theorem projection_iso_of_property
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A))
    (h : ProEtale.HasProjectionFormulaOfCompactification A c K L) :
    IsIso (((ProEtale.projectionMapOfCompactification A c).app K).app L) := h

attribute [local irreducible] ProEtale.HasProjectionFormulaOfCompactification

set_option linter.style.haveILetI false in
private theorem map_isIso_of_proof
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N : C} (f : M ⟶ N) (hf : IsIso f) : IsIso (F.map f) := by
  letI := hf
  exact F.map_isIso f

end AlgebraicGeometry.ProEtale.SpTowerProjection
