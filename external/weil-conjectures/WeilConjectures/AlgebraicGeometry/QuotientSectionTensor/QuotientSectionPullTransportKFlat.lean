/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportKFlatOrdinary
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportKFlatDerived

/-! # Flat-term part of normalized quotient section pull transport

## References

* Stacks 06YS, 06YY, 0D6D and 0G7E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

attribute [local semireducible] QuotientChange.L
attribute [local implicit_reducible] QuotientChange.L

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

private def sectionPullTransportDerived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) :
    cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T := by
  let e : (derivedEquivalence Λ Y).functor ⋙
        (cY.model.T ⋙ derivedPullback Λ' f) ≅
      (derivedEquivalence Λ Y).functor ⋙
        (derivedPullback Λ f ⋙ cX.model.T) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cY.derived.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (scalarSectionPullComparison Λ' f).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight lam (derivedEquivalence Λ' X).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ cX.derived ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (scalarSectionPullComparison Λ f) _ ≪≫
      Functor.associator _ _ _
  exact ((Functor.whiskeringLeft _ _ _).obj
    (derivedEquivalence Λ Y).functor).preimageIso e

private theorem sectionPullTransportDerived_realization (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : ScalarSectionData φ U) (sV : ScalarSectionData φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (M : DerivedCategory (Modules Λ V)) :
    (derivedEquivalence Λ' U).functor.map (b.hom.app M) ≫
        sU.derived.hom.app ((L Λ h).obj M) ≫
        sU.model.T.map ((scalarSectionPullComparison Λ h).hom.app M) =
      (scalarSectionPullComparison Λ' h).hom.app ((D φ V).obj M) ≫
        (derivedPullback Λ' h).map (sV.derived.hom.app M) ≫
        (sectionPullTransportDerived φ h sU sV b).hom.app
          ((derivedEquivalence Λ V).functor.obj M) := by
  have he := congrArg (fun t ↦ t.app M)
    (((Functor.whiskeringLeft _ _ _).obj
      (derivedEquivalence Λ V).functor).map_preimage
        (show (derivedEquivalence Λ V).functor ⋙
            (sV.model.T ⋙ derivedPullback Λ' h) ⟶
          (derivedEquivalence Λ V).functor ⋙
            (derivedPullback Λ h ⋙ sU.model.T) from
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight sV.derived.symm _ ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (scalarSectionPullComparison Λ' h).symm ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight b _ ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ sU.derived ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (scalarSectionPullComparison Λ h) _ ≪≫
            Functor.associator _ _ _).hom))
  change (sectionPullTransportDerived φ h sU sV b).hom.app
      ((derivedEquivalence Λ V).functor.obj M) = _ at he
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  erw [Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

/-- The flat-term fragment of `SectionPullNormalized`. It retains the ordinary
section square and requires the derived computation square only on the flat-term
K-flat representatives used by localization descent.
-/
def SectionPullNormalizedOnKFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T) : Prop :=
  ∃ e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E,
    (∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) ∧
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)

/-- Flat-term construction of the normalized section pullback comparison. -/
theorem section_pull_transport_section_normalized_kflat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam) :
    ∃ barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T,
      SectionPullNormalizedOnKFlat a f cX cY barLam := by
  let barLam := sectionPullTransportDerived a f cX cY lam
  refine ⟨barLam, ?_⟩
  obtain ⟨e, he⟩ := section_pull_transport_kflat_ordinary a f cX cY hcX hcY
  refine ⟨e, he, ?_⟩
  exact section_pull_transport_kflat_derived a f cX cY hcX hcY lam hlam barLam
    (sectionPullTransportDerived_realization a f cX cY lam) e he

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
