/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonCoefficients
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonPresentationSupport
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.ConstructibleSheaf.KernelCokernel

set_option linter.privateModule false

/-! # Coefficient presentation of the finite comparison predicates

Source: blueprint finite comparison, coefficient paragraph, and Stacks Tags 03CY,
09AJ and 09AL (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u c d h k w
open CategoryTheory CategoryTheory.Limits
section FiniteComparisonProof

-- Fix the coefficient universes only within these private proofs.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify

-- Prefer the actual coefficient size to imported maximum-universe size instances.
private local instance (priority := 2000) presentationSiteSmall
    (X : AlgebraicGeometry.Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} _

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

open MonoidalCategory
open scoped CategoryTheory.Obj

-- Keep the private entry points used by existing `import all` consumers.
open InternalAbelianSheafModule in
private theorem sectionMonoidal_exists
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [UnivLE.{max c h, w}] [HasSheafify J Ab.{w}]
    [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Sheaf J Ab.{w}) [MonObj R] [IsCommMonObj R] :
    Nonempty (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.Monoidal := by
  exact FiniteComparisonPresentationSupport.sectionMonoidal_exists J R

private def localFinite {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ (U : C) (f : U ⟶ V), S f →
    ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
      Nonempty (F.over U ≅ (constantSheaf (J.over U) (ModuleCat.{w} A)).obj M)

private theorem localFinite_iso
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    {F G : Sheaf J (ModuleCat.{w} A)} (e : F ≅ G) (hF : localFinite J A F) :
    localFinite J A G := by
  exact FiniteComparisonPresentationSupport.localFinite_iso J A e hF

private def finiteModelSieve {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) (V : C) : Sieve V where
  arrows U _ := ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
    Nonempty (F.over U ≅ ((constantSheaf J (ModuleCat.{w} A)).obj M).over U)
  downward_closed := by
    rintro U W f ⟨M, hM, ⟨e⟩⟩ g
    let G := (constantSheaf J (ModuleCat.{w} A)).obj M
    exact ⟨M, hM, ⟨(F.pushforwardOverMapIso g).symm ≪≫
      (J.overMapPullback (ModuleCat.{w} A) g).mapIso e ≪≫ G.pushforwardOverMapIso g⟩⟩

private theorem localFinite_iff_sieve
    {C : Type c} [Category.{h} C] [HasTerminal C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ (U : C) (P : (Over U)ᵒᵖ ⥤ ModuleCat.{w} A),
      (Over.forget U).op.HasPointwiseRightKanExtension P]
    (F : Sheaf J (ModuleCat.{w} A)) :
    localFinite J A F ↔ finiteModelSieve J A F (⊤_ C) ∈ J (⊤_ C) := by
  exact FiniteComparisonPresentationSupport.localFinite_iff_sieve J A F

open FiniteComparisonPresentationSupport hiding sectionMonoidal_exists localFinite
  localFinite_iso finiteModelSieve localFinite_iff_sieve

attribute [local irreducible]
  FiniteComparisonPresentationSupport.monoidalOfOplaxIsos
  FiniteComparisonPresentationSupport.sectionMonoidal
  FiniteComparisonPresentationSupport.monoidalOfAdjointEquivalence
  FiniteComparisonPresentationSupport.monoidalOfInverse
  FiniteComparisonPresentationSupport.constantScalarMonoidal
  FiniteComparisonPresentationSupport.ringScalarMonoidal

attribute [local instance]
  CategoryTheory.moduleMonoidal CategoryTheory.moduleSymmetric
  CategoryTheory.moduleClosed CategoryTheory.modulePreadditive CategoryTheory.moduleGrothendieck
  CategoryTheory.flatResolution CategoryTheory.standardDerived

private local instance coefficientFixedMonoidal
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A] : (coefficientModelFixedScalars J A).Monoidal := by
  letI : (ConstantScalarRestriction.restriction J A).Monoidal :=
    (ConstantScalarRestriction.ordinary J A).braided.toMonoidal
  let i : ConstantScalarRestriction.restriction J A ≅ coefficientModelFixedScalars J A :=
    CategoryTheory.restrictionIso J A
  exact Functor.Monoidal.transport i

namespace AlgebraicGeometry.ProEtale

private def etaleSites (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) (ModuleCat.{u + 1} A) ≌
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  letI : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  letI : e.inverse.IsDenseSubsite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) X.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
      X.Etale).IsDenseSubsite
        ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
          X.Etale).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)
  exact (e.sheafCongr X.smallEtaleTopology
    (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) (ModuleCat.{u + 1} A)).symm

private local instance etaleSites_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (etaleSites X A).functor.Monoidal := by
  let G : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤ X.Etale := AsSmall.down
  letI : G.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)).isEquivalence_inverse
  let J := Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X
  let K := X.smallEtaleTopology
  let L := Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} A) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{u + 1} A) J K
  letI : L.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal G (ModuleCat.{u + 1} A) J K
  exact monoidalOfAdjointEquivalence (etaleSites X A) L adj

private theorem etaleSites_localFinite
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X)
      (ModuleCat.{u + 1} A)) :
    IsCoefficientModelLocallyConstantFinite _ A F ↔
      localFinite X.smallEtaleTopology A ((etaleSites X A).functor.obj F) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  let : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  let : e.inverse.IsDenseSubsite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) X.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
      X.Etale).IsDenseSubsite
        ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
          X.Etale).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)
  let : e.functor.IsDenseSubsite X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) := by
    infer_instance
  let : e.symm.inverse.IsDenseSubsite X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) :=
    inferInstanceAs (e.functor.IsDenseSubsite _ _)
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} A) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  exact localFinite_site_equivalence _ _ e.symm A F

private def etaleSitePullbackSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    Scheme.coefficientEtaleFixedPullback.{u, u + 1} f A ⋙ (etaleSites X A).functor ≅
      (etaleSites Y A).functor ⋙ Etale.upperStar (ModuleCat.{u + 1} A) f := by
  let R := (Scheme.coefficientEtaleBaseChange.{u, u + 1} f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} A) (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} Y)
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X)
  let i : R ⋙ (etaleSites Y A).functor ≅
      (etaleSites X A).functor ⋙ Etale.lowerStar (ModuleCat.{u + 1} A) f :=
    NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ Iso.refl _)))
  exact leftSquareOfRight _ R
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)
    _ _ (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (etaleSites Y A) (etaleSites X A) i

private def proSites (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ModuleCat.{u + 1} A) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  letI : (AsSmall.down : AsSmall.{u + 1} X.ProEt ⥤ X.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  letI : e.inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
      X.ProEt).IsDenseSubsite
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
          X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X))
  exact (e.sheafCongr (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ModuleCat.{u + 1} A)).symm

private local instance proSites_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (proSites X A).functor.Monoidal := by
  let G : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤ X.ProEt := AsSmall.down
  letI : G.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_inverse
  let J := Scheme.coefficientProEtaleModelTopology.{u, u + 1} X
  let K := (Scheme.ProEt.topology X)
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let L := Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} A) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{u + 1} A) J K
  letI : L.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal G (ModuleCat.{u + 1} A) J K
  exact monoidalOfAdjointEquivalence (proSites X A) L adj

private theorem coefficient_etale_global
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :
    Scheme.IsCoefficientConstructibleEtaleModule.{u, u + 1} X A F ↔
      ∃ S : Scheme.Stratification X, ∀ i,
        IsCoefficientModelLocallyConstantFinite
          (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} (S.domain i)) A
          ((Scheme.coefficientEtaleFixedPullback.{u, u + 1} (S.immersion i) A).obj
            ((coefficientModelFixedScalars _ A).obj F)) := by
  let P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop := fun {Y} f ↦
    IsCoefficientModelLocallyConstantFinite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} Y) A
      ((Scheme.coefficientEtaleFixedPullback.{u, u + 1} f A).obj
        ((coefficientModelFixedScalars _ A).obj F))
  have h := Scheme.affine_local_stratification_iff X P
    (fun f g h ↦ Scheme.etaleFinite_comp f g A _ h)
  constructor
  · intro hF
    obtain ⟨S, _, hS⟩ := h.mp (fun U hU ↦ by
      obtain ⟨S, hc, hS⟩ := hF U hU
      exact ⟨Scheme.constructibleStratification S hc, hc, hS⟩)
    exact ⟨S, hS⟩
  · rintro ⟨S, hS⟩ U hU
    obtain ⟨T, hc, hT⟩ := h.mpr ⟨S, S.isConstructible_stratum, hS⟩ U hU
    exact ⟨Scheme.finiteStratification T, hc, hT⟩

private theorem etale_constructible_iso
    {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A] [Finite A]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (e : F ≅ G)
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    Scheme.IsConstructibleEtaleModuleSheaf G := by
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr
    (Scheme.IsConstructibleSheaf.of_iso e)

private local instance etale_bounded_iso
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    (Etale.DerivedCategory.isBoundedConstructible A X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨fun q ↦ etale_constructible_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e) (h.1 q), ?_⟩
    obtain ⟨a, b, hab, hz⟩ := h.2
    exact ⟨a, b, hab, fun q hq ↦ (hz q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e).symm⟩

private local instance etaleRealization_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (finiteComparisonEtaleModelRealization X A).Monoidal :=
  inferInstanceAs (coefficientModelFixedScalars _ A ⋙ (etaleSites X A).functor).Monoidal

private local instance proRealization_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (finiteComparisonProEtaleModelRealization X A).Monoidal :=
  inferInstanceAs (coefficientModelFixedScalars _ A ⋙ (proSites X A).functor).Monoidal

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

omit [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] [Finite B] in
private theorem fixedModuleLimits :
    HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

attribute [local instance] fixedModuleLimits

private theorem modelOfIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X N) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (C.f i)).mapIso e ≪≫ eP⟩⟩

section InternalRealization

variable (X : Scheme.{u})
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
      Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

private def realizedSectionRing := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
  (Scheme.ProEt.topology X) (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)

private def realizedSectionUnit :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)) ⟶
      (realizedSectionRing B X).obj := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let P := (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of R)
  let mP := (Functor.const X.ProEtᵒᵖ).monObjObj (AddCommGrpCat.of R)
  let mQ := Sheaf.monObj_presheafToSheaf_obj J
    (((Functor.const X.ProEtᵒᵖ).obj (RingCat.of R)) ⋙ forget₂ RingCat Ab)
  have hm : (presheafToSheaf J Ab.{u + 1}).monObjObj P = mQ := by
    exact congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
      (presheafToSheaf J Ab.{u + 1}) _ _ m) (constantRingMonObj (C := X.ProEtᵒᵖ) R)
  let f := (finiteDiscreteSchemeRingIso B X eR).hom
  have hf := IsMonHom.of_eq f hm.symm rfl (hf := (inferInstance : IsMonHom f))
  have hu := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
  have hmap := FiniteDiscreteOrdinary.monHomMapExplicit (sheafToPresheaf J Ab.{u + 1})
    ((presheafToSheaf J Ab.{u + 1}).monObjObj P) _ f hf
  let φ := toSheafify J P ≫ f.hom
  letI : @IsMonHom _ _ _ _ _ mP
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)) φ :=
    FiniteDiscreteOrdinary.monHomCompExplicit mP _ _ _ _ hu hmap
  exact FiniteDiscreteOrdinary.constantSectionRingMapAux J R
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) φ

private def realizedSectionMap :
    realizationRing (Scheme.ProEt.topology X) (ULift.{u + 1} B) ⟶ realizedSectionRing B X :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv _
    (realizedSectionRing B X)).symm (realizedSectionUnit B X eR)

omit [DiscreteTopology B] [Finite B] in
private theorem realizedSectionMap_unit (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} B) :
    (realizedSectionMap B X eR).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))).app U a) =
      (finiteDiscreteSchemeRingIso B X eR).hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app U a) := by
  exact ConcreteCategory.congr_hom (congr_app
    (((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv _
      (realizedSectionRing B X)).apply_symm_apply (realizedSectionUnit B X eR)) U) a

private local instance realizedSectionMap_isIso : IsIso (realizedSectionMap B X eR) := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  let F := sheafCompose J V
  have : J.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification J V
  let e := (constantCommuteCompose J V).app (CommRingCat.of R)
  let g := F.map (realizedSectionMap B X eR)
  have hg : e.inv ≫ g = (finiteDiscreteSchemeRingIso B X eR).hom := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X).property
    have he : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (V.obj (CommRingCat.of R))) ≫
        e.inv.hom = Functor.whiskerRight
          (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of R))) V := by
      change _ ≫ (sheafifyMap J (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of R) V).inv ≫
        (sheafifyComposeIso J V _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    change _ ≫ (e.inv.hom ≫ g.hom) = _
    rw [← Category.assoc, he]
    ext U a
    exact realizedSectionMap_unit B X eR U a
  have : IsIso (e.inv ≫ g) := hg.symm ▸ inferInstance
  have : IsIso g := by
    have hh : g = e.hom ≫ (e.inv ≫ g) := by simp
    rw [hh]
    infer_instance
  exact isIso_of_reflects_iso (realizedSectionMap B X eR) F

@[irreducible] private def realizedConstantCounit (X : Scheme.{u}) :
    finiteComparisonConstantRealization X B ⋙
      ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology X)
        (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) rfl ≅ 𝟭 _ := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let A := ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) R
  let G := internalToModule R
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R G rfl
  let L := finiteComparisonConstantRealization X B
  let E := sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙ finiteComparisonPresheaf X B
  let P := ConstantInternalModuleSheafEncoding.modulePresheafEncoding (C := X.ProEt) R G
  let adj := (sheafificationAdjunction J Ab.{u + 1}).mapModAdjunction A
  have hu (M : Sheaf J (ModuleCat.{u + 1} R)) : IsIso (adj.unit.app (E.obj M)) := by
    rw [← isIso_iff_of_reflects_iso _ (Mod.forget A)]
    change IsIso ((adj.unit.app (E.obj M)).hom)
    rw [Adjunction.mapModAdjunction_unit_app_hom]
    exact isIso_toSheafify J
      ((sheafCompose J (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj M).property
  let η := Functor.whiskerRight (Functor.whiskerLeft E adj.unit) P
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Functor.map_isIso P (adj.unit.app (E.obj M))
  let e0 : E ⋙ P ≅ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    Functor.isoWhiskerLeft _ (finiteComparisonPresheafEncodingIso X B)
  let e : (L ⋙ H) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) ≅
      (𝟭 _) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    (asIso η).symm ≪≫ e0
  exact ((fullyFaithfulSheafToPresheaf J (ModuleCat.{u + 1} R)).whiskeringRight _)
    |>.preimageIso e

@[irreducible] private def realizedEncodingIso :
    finiteComparisonRealization B X eR ≅
      (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
        (internalToModule (ULift.{u + 1} B)) rfl X).functor := by
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology X)
    (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) rfl
  let i : finiteComparisonConstantRealization X B ≅ H.inv :=
    Iso.isoCompInverse (H := H.asEquivalence) (realizedConstantCounit B X) ≪≫
      Functor.leftUnitor H.inv
  unfold finiteComparisonRealization CondensedRing.finiteDiscreteCoefficientEquivalence
  exact Functor.isoWhiskerRight i
      (Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv) ≪≫
    Functor.isoWhiskerLeft H.inv (Mod.comapCongr (by
      apply (cancel_mono (finiteDiscreteSchemeRingIso B X eR).hom).mp
      simp))

private def realizedInverse :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) ⥤
        Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)).functor ⋙
    SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (realizedSectionMap B X eR) ⋙
    ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) (ULift.{u + 1} B)

omit [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] [Finite B] in
private theorem realizedFixedUnit (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} B) :
    (((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of (ULift.{u + 1} B))).hom.app U)
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B)))).app U a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))).app U a := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let e := (constantCommuteCompose J V).app (CommRingCat.of R)
  have he : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (V.obj (CommRingCat.of R))) ≫
      e.inv.hom = Functor.whiskerRight
        (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of R))) V := by
    change _ ≫ (sheafifyMap J (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of R) V).inv ≫
      (sheafifyComposeIso J V _).hom) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
    ext U a
    rfl
  exact ConcreteCategory.congr_hom (congr_app he U) a

@[irreducible] private def realizedInverseIso :
    realizedInverse B X eR ≅
      (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
        (internalToModule (ULift.{u + 1} B)) rfl X).inverse := by
  unfold CondensedRing.finiteDiscreteCoefficientEquivalence
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
    ext m
    symm
    change (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)
      M.X).hom.app U
        (((Functor.LaxMonoidal.μ
          (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) M.X).app U)
          (_ ⊗ₜ[ℤ] m)) = _
    erw [realizedFixedUnit B X, realizedSectionMap_unit B X eR]
    change _ = (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((ConstantInternalModuleSheafEncoding.presheafToFunctor
        (C := X.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
          ((ConstantInternalModuleSheafEncoding.moduleLocalizationRight
            (Scheme.ProEt.topology X)
            (ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ)
              (ULift.{u + 1} B))).obj
                ((Mod.comap (finiteDiscreteSchemeRingIso B X eR).hom).obj M))).obj U).X).hom
                  (a ⊗ₜ[ℤ] m)
    rw [CondensedRing.encoding_action B eR X M U]
    simp only [AddCommGrpCat.comp_apply]
    rfl
  · intro U V f
    ext m
    rfl
  · intro M N f
    ext U m
    rfl

-- The auxiliary coefficient instances have an undetermined max universe here.
-- Use the same constructions at the fixed coefficient universe in this helper.
attribute [-instance]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
omit [DiscreteTopology B] [Finite B] in
private theorem realizedInverseMonoidal_exists :
    Nonempty (realizedInverse B X eR).Monoidal := by
  let J := Scheme.ProEt.topology X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify J Ab.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : J.WEqualsLocallyBijective Ab.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  exact sectionScalarComposite_exists.{u + 1, u} J (ULift.{u + 1} B)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)
    (realizedSectionMap B X eR)

omit [DiscreteTopology B] [Finite B] in
private theorem finiteRealizationMonoidal_exists :
    Nonempty (finiteComparisonRealization B X eR).Monoidal := by
  let E := CondensedRing.finiteDiscreteCoefficientEquivalence B eR
    (internalToModule (ULift.{u + 1} B)) rfl X
  exact monoidalOfInverse_exists E (finiteComparisonRealization B X eR)
    (realizedInverse B X eR) (realizedInverseMonoidal_exists B X eR)
    (realizedEncodingIso B X eR) (realizedInverseIso B X eR)

private local instance finiteRealizationMonoidal :
    (finiteComparisonRealization B X eR).Monoidal :=
  Classical.choice (finiteRealizationMonoidal_exists B X eR)

omit [DiscreteTopology B] [Finite B] in
private theorem constantConstructible_iso
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified
      (Profinite.continuousMapRingObj.{u} B) X M) :
    IsFiniteConstantStratified (Profinite.continuousMapRingObj.{u} B) X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun i ↦ modelOfIso _
    ((CondensedRing.upperStar _ (S.immersion i)).mapIso e.symm) (hS i)⟩

end InternalRealization

attribute [local instance] finiteRealizationMonoidal

private local instance constantModel_bounded_iso
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible
      (Profinite.continuousMapRingObj.{u} B) X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1, fun q ↦ ?_⟩
    classical
    have hh := h.2 q
    have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
    simp only [IsConstantModelConstructible, ite_eq_left hX] at hh ⊢
    exact constantConstructible_iso B X ((DerivedCategory.homologyFunctor _ q).mapIso e) hh

end AlgebraicGeometry.ProEtale

end FiniteComparisonProof

namespace AlgebraicGeometry.ProEtale

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

end AlgebraicGeometry.ProEtale
