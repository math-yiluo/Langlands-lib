/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex


public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomology
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Coherent higher direct images with proper support

Source: Stacks Project, Cohomology of Schemes, Tag 08DS,
Lemma `coherent-lemma-support-proper-over-base-pushforward`
(blueprint: lem-pc-coherent-support-proper-higher-direct-image).
-/

@[expose] public section

universe u wX wS

open CategoryTheory

namespace AlgebraicGeometry

private theorem qc_single {X : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent) :
    schemeDerivedQCohProperty X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have hzero : Limits.IsZero
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_isZero
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi

private theorem finitePresentation_of_quasicoherent_finiteType
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] (F : Y.Modules)
    (hq : F.IsQuasicoherent) (ht : F.IsFiniteType) : F.IsFinitePresentation := by
  have hc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y F).mpr
    ⟨hq, ht⟩
  have hfp (U : Y.affineOpens) : (F.over U.1).IsFinitePresentation := by
    have := IsLocallyNoetherian.component_noetherian U
    have := Scheme.Modules.coherent_affine_sections_finite Y F hc U.1 U.2
    have hp := Module.finitePresentation_of_finite Γ(Y, U.1) Γ(F, U.1)
    exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} Y).2 F hq).1 U.1 U.2).2.mpr hp
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _ F
    Y.affineOpens (fun U ↦ U.1) (by
      rw [Opens.coversTop_iff]
      exact iSup_affineOpens_eq_top Y) hfp

/-- A coherent module whose support is proper over a locally Noetherian base has coherent
higher direct images along a locally finite type morphism in every nonnegative degree.
Source: Stacks Project, Cohomology of Schemes, Tag 08DS
(blueprint: lem-pc-coherent-support-proper-higher-direct-image).

Proof:
1. By `lem-weil-pbc-module-support-proper-over-base` (Tag 0CYS), choose a closed immersion
   i : Z → X and a finite type quasi-coherent module G on Z with i_*G ≅ F, such that
   g = i ≫ f is proper.
2. A closed immersion is affine by `lem-weil-pbc-closed-immersion-integral-separated-uc`.
   Thus `lem-pc-affine-morphism-hi` gives R^q i_*G = 0 for q > 0. Derived direct-image
   composition (`lem-pc-derived-direct-image-composition`) identifies Rf_*F with Rg_*G,
   hence identifies their p-th cohomology sheaves.
3. The proper morphism g is locally of finite type, so Z is locally Noetherian by
   `pqf-lem-locnoeth-lft`. The finite type quasi-coherent G is coherent by
   `pqf-lem-coherent-ft-locnoeth`. Apply `lem-pc-coherent-hi` (Tag 02O5) to g and G,
   and transfer coherence through the isomorphism of step 2. -/
theorem isCoherent_schemeModuleHigherDirectImage_of_support_proper
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupport : Scheme.Modules.HasSupportProperOver f F) (p : ℤ) (hp : 0 ≤ p) :
    RingedSpace.IsCoherent S.toRingedSpace ((schemeModuleHigherDirectImage f p).obj F) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hqc, hft⟩ :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have := hqc
  have := hft
  obtain ⟨Z, i, hi, hg, _, G, hGqc, hGft, ⟨eF⟩⟩ :=
    (Scheme.Modules.module_support_proper_over_base f F).2.1.mp hSupport
  have := hi
  have := hg
  have := hGqc
  have := hGft
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have : G.IsFinitePresentation :=
    finitePresentation_of_quasicoherent_finiteType Z G hGqc hGft
  have : IsGrothendieckAbelian.{u} Z.Modules := Scheme.Modules.isGrothendieckAbelian Z
  let AZ := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let AX := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let AS := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let : HasDerivedCategory AZ := HasDerivedCategory.standard AZ
  let EG := (DerivedCategory.singleFunctor AZ 0).obj G
  let EI := (schemeDerivedDirectImage i).obj EG
  have hEG : schemeDerivedQCohProperty Z EG := qc_single G hGqc
  have hEI (j : ℤ) (hj : j ≠ 0) :
      Limits.IsZero ((DerivedCategory.homologyFunctor AX j).obj EI) := by
    obtain ⟨⟨ej⟩, _⟩ := schemeHigherDirectImage_of_affine i EG hEG j
    have hz : Limits.IsZero ((DerivedCategory.homologyFunctor AZ j).obj EG) := by
      rcases lt_or_gt_of_ne hj with hj | hj
      · exact DerivedCategory.isZero_of_isGE EG 0 j hj
      · exact DerivedCategory.isZero_of_isLE EG 0 j hj
    exact ((RingedSpace.moduleDirectImage i.toLRSHom.toShHom).map_isZero hz).of_iso ej
  have : EI.IsGE 0 := (DerivedCategory.isGE_iff EI 0).2 (fun j hj ↦ hEI j (by omega))
  have : EI.IsLE 0 := (DerivedCategory.isLE_iff EI 0).2 (fun j hj ↦ hEI j (by omega))
  obtain ⟨V, ⟨eV⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE EI 0
  obtain ⟨⟨eI⟩, _⟩ := schemeHigherDirectImage_of_affine i EG hEG 0
  let e₀ := (DerivedCategory.homologyFunctor AX 0).mapIso eV ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AX 0).app V
  let e₁ := eI ≪≫ (RingedSpace.moduleDirectImage i.toLRSHom.toShHom).mapIso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso AZ 0).app G)
  let eVF : V ≅ F := e₀.symm ≪≫ e₁ ≪≫ eF.symm
  let eIF := eV ≪≫ (DerivedCategory.singleFunctor AX 0).mapIso eVF
  obtain ⟨ecomp⟩ := derivedDirectImageComposition i f
  let eout := ecomp.app EG ≪≫ (schemeDerivedDirectImage f).mapIso eIF
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by omega⟩
  have hfp := Scheme.Modules.isFinitePresentation_higherDirectImage (i ≫ f) G n
  let eR := (DerivedCategory.homologyFunctor AS n).mapIso eout
  let eG := Functor.homologyRightDerivedFunctorObjSingleFunctorIso
    (RingedSpace.moduleDirectImage (i ≫ f).toLRSHom.toShHom) G n
  let e : (Scheme.Modules.higherDirectImage (i ≫ f) n).obj G ≅
      (schemeModuleHigherDirectImage f n).obj F := eG.symm ≪≫ eR
  have : ((schemeModuleHigherDirectImage f n).obj F).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation S.ringCatSheaf).prop_of_iso e hfp
  exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType S _).mpr
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
