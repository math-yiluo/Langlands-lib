/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-! # Transport of a quasi-coherent direct-image adjunction to standard localizations

Source: Stacks Project, Tags 05RU and 079V.
(blueprint: lem-pc-derived-qcoh-standard-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u wZ wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Quasi-coherence of homology is invariant under ambient isomorphisms. -/
private instance qcohClosed (X : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    (schemeDerivedQCohProperty X).IsClosedUnderIsomorphisms where
  of_iso e h n := (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).mapIso e) (h n)

/-- The standard comparison commutes with the localization of complexes. -/
private noncomputable def qComparison (X : Scheme.{u})
    (h : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    @DerivedCategory.Q _ _ _ h ⋙ (@schemeDerivedStandardEquivalence X h).functor ≅
      @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let s := HasDerivedCategory.standard A
  let E := @schemeDerivedStandardEquivalence X h
  exact (Functor.isoWhiskerRight (@DerivedCategory.quotientCompQhIso A _ _ h)
      E.functor).symm ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Localization.compUniqFunctor (@DerivedCategory.Qh A _ _ h)
        (@DerivedCategory.Qh A _ _ s) (HomotopyCategory.quasiIso A (.up ℤ))) ≪≫
    @DerivedCategory.quotientCompQhIso A _ _ s

/-- Homology commutes with the standard comparison by uniqueness of localization lifts. -/
private noncomputable def homologyComparison (X : Scheme.{u})
    (h : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (n : ℤ) :
    (@schemeDerivedStandardEquivalence X h).functor ⋙
        @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n ≅
      @DerivedCategory.homologyFunctor _ _ _ h n := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let s := HasDerivedCategory.standard A
  let H := @DerivedCategory.homologyFunctor A _ _ s n
  let α := (Functor.associator (@DerivedCategory.Q A _ _ h) _ H).symm ≪≫
    Functor.isoWhiskerRight (qComparison X h) H ≪≫
      @DerivedCategory.homologyFunctorFactors A _ _ s n
  let β := @DerivedCategory.homologyFunctorFactors A _ _ h n
  exact (Localization.fullyFaithfulWhiskeringLeft (@DerivedCategory.Q A _ _ h)
    (HomologicalComplex.quasiIso A (.up ℤ)) A).preimageIso (α ≪≫ β.symm)

/-- Restrict the standard comparison to quasi-coherent objects. -/
private noncomputable def qcohEquivalence (X : Scheme.{u})
    (h : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    @schemeDerivedQCohCategory X h ≌
      @schemeDerivedQCohCategory X (HasDerivedCategory.standard _) := by
  let E := @schemeDerivedStandardEquivalence X h
  apply E.congrFullSubcategory
  funext K
  apply propext
  change (∀ n : ℤ, _) ↔ (∀ n : ℤ, _)
  apply forall_congr'
  intro n
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_iff_of_iso
    ((homologyComparison X h n).app K)

/-- K-injective computations of pushforward use the same resolution before localization. -/
private theorem directImageComparison {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (hZ : HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
    (hY : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) :
    Nonempty (@schemeDerivedDirectImage Z Y hZ hY i ⋙
        (@schemeDerivedStandardEquivalence Y hY).functor ≅
      (@schemeDerivedStandardEquivalence Z hZ).functor ⋙
        @schemeDerivedDirectImage Z Y (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) i) := by
  let AZ := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let AY := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let sZ := HasDerivedCategory.standard AZ
  let sY := HasDerivedCategory.standard AY
  let qZ := @DerivedCategory.Q AZ _ _ hZ
  let eY := (@schemeDerivedStandardEquivalence Y hY).functor
  let R := @schemeDerivedDirectImage Z Y hZ hY i
  let RS := @schemeDerivedDirectImage Z Y sZ sY i
  obtain ⟨α⟩ := @RingedSpace.derivedModuleDirectImageFactorization _ _ hZ hY
    i.toLRSHom.toShHom
  obtain ⟨β⟩ := @RingedSpace.derivedModuleDirectImageFactorization _ _ sZ sY
    i.toLRSHom.toShHom
  let F := CochainComplex.kInjectiveResolutionFunctor.{u} AZ ⋙
    (RingedSpace.moduleDirectImage i.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let δ : qZ ⋙ (R ⋙ eY) ≅ F ⋙ @DerivedCategory.Q AY _ _ sY :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α eY ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (qComparison Y hY)
  let γ : qZ ⋙ ((@schemeDerivedStandardEquivalence Z hZ).functor ⋙ RS) ≅
      F ⋙ @DerivedCategory.Q AY _ _ sY :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (qComparison Z hZ) RS ≪≫ β
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft qZ
    (HomologicalComplex.quasiIso AZ (.up ℤ)) (@schemeDerivedCategory Y sY)).preimageIso
      (δ ≪≫ γ.symm)⟩

/-- Standardize a specified right adjoint, with comparisons on all objects.
Source: Stacks Project, Tags 05RU and 079V.
(blueprint: lem-pc-derived-qcoh-standard-adjunction).

Proof: homology is the localization lift of homotopy-category homology. Uniqueness
of localization lifts identifies homology after the standard comparison, in both
directions. Quasi-coherence is therefore preserved, and the ambient equivalences
restrict to equivalences eZ and eY of the full quasi-coherent subcategories. The
K-injective factorization of module pushforward identifies its two models:
both use the same functorial resolution and termwise pushforward before target
localization. Compare these factorizations using the Q comparison, then descend
the natural isomorphism by full faithfulness of precomposition with Q. This comparison transfers hRi
to the standard model. Conjugate the given adjunction by eZ and eY, and identify
its left adjoint with the standard restricted direct image. Take the resulting
right adjoint cS = eY.inverse followed by c and eZ.functor. The unit of eY and the
inclusion comparisons give the displayed natural isomorphisms. This construction
uses no tensor formula, perfection, properness, or immersion assumption. The
adjunction specifies cS up to natural isomorphism. Identity maps and zero module
categories are covered by the same equivalence and Kan-extension arguments. -/
theorem derivedQCoh_standardAdjunction
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hRi : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage i).obj E.obj))
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adjC : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i) hRi ⊣ c) :
    ∃ (eY : schemeDerivedQCohCategory Y ≌
        @schemeDerivedQCohCategory Y (HasDerivedCategory.standard _))
      (hRiS : ∀ E : @schemeDerivedQCohCategory Z (HasDerivedCategory.standard _),
        @schemeDerivedQCohProperty Y (HasDerivedCategory.standard _)
          ((@schemeDerivedDirectImage Z Y (HasDerivedCategory.standard _)
            (HasDerivedCategory.standard _) i).obj E.obj))
      (cS : @schemeDerivedQCohCategory Y (HasDerivedCategory.standard _) ⥤
        @schemeDerivedQCohCategory Z (HasDerivedCategory.standard _)),
      Nonempty ((@schemeDerivedQCohProperty Y (HasDerivedCategory.standard _)).lift
        ((@schemeDerivedQCohProperty Z (HasDerivedCategory.standard _)).ι ⋙
          @schemeDerivedDirectImage Z Y (HasDerivedCategory.standard _)
            (HasDerivedCategory.standard _) i) hRiS ⊣ cS) ∧
      Nonempty (eY.functor ⋙
        (@schemeDerivedQCohProperty Y (HasDerivedCategory.standard _)).ι ≅
        (schemeDerivedQCohProperty Y).ι ⋙ (schemeDerivedStandardEquivalence Y).functor) ∧
      Nonempty ((eY.functor ⋙ cS) ⋙
        (@schemeDerivedQCohProperty Z (HasDerivedCategory.standard _)).ι ≅
        (c ⋙ (schemeDerivedQCohProperty Z).ι) ⋙
          (schemeDerivedStandardEquivalence Z).functor) := by
  let hZ : HasDerivedCategory.{wZ}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) := inferInstance
  let hY : HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := inferInstance
  let sZ := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let sY := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let PZ := @schemeDerivedQCohProperty Z sZ
  let PY := @schemeDerivedQCohProperty Y sY
  let eZ := @schemeDerivedStandardEquivalence Z hZ
  let eY := @schemeDerivedStandardEquivalence Y hY
  let qZ := qcohEquivalence Z hZ
  let qY := qcohEquivalence Y hY
  let R := @schemeDerivedDirectImage Z Y hZ hY i
  let RS := @schemeDerivedDirectImage Z Y sZ sY i
  obtain ⟨δ⟩ := directImageComparison i hZ hY
  let ε : (eZ.inverse ⋙ R) ⋙ eY.functor ≅ RS :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft eZ.inverse δ ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eZ.counitIso RS ≪≫ Functor.leftUnitor RS
  have hRiS : ∀ E : PZ.FullSubcategory, PY (RS.obj E.obj) := by
    intro E
    let B : @schemeDerivedQCohCategory Y hY :=
      ⟨R.obj (qZ.inverse.obj E).obj, hRi (qZ.inverse.obj E)⟩
    exact PY.prop_of_iso (ε.app E.obj) (qY.functor.obj B).property
  let r := (@schemeDerivedQCohProperty Y hY).lift
    ((@schemeDerivedQCohProperty Z hZ).ι ⋙ R) hRi
  let rS := PY.lift (PZ.ι ⋙ RS) hRiS
  let ν : (qZ.inverse ⋙ r) ⋙ qY.functor ≅ rS :=
    (PY.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft PZ.ι ε)
  let cS := qY.inverse ⋙ (c ⋙ qZ.functor)
  let adjS : rS ⊣ cS :=
    ((qZ.symm.toAdjunction.comp adjC).comp qY.toAdjunction).ofNatIsoLeft ν
  refine ⟨qY, hRiS, cS, ⟨adjS⟩, ⟨Iso.refl _⟩, ?_⟩
  let T := (c ⋙ (@schemeDerivedQCohProperty Z hZ).ι) ⋙ eZ.functor
  exact ⟨Functor.isoWhiskerRight qY.unitIso.symm T ≪≫ Functor.leftUnitor T⟩

end AlgebraicGeometry
