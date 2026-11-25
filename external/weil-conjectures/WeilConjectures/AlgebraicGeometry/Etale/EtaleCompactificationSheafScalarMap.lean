/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactificationGraphMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumStalks
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import all WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleProjectionSectionNormalization
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFiniteCompactificationSheafIso
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-! # The ordinary compactified étale coefficient mate on sheet generators

Source: Stacks Project, more-etale.tex, Tags 0GKF and 0GL6;
etale-cohomology.tex, Tags 03S5 and 0F4L; sites-modules.tex, Tag 03EL
(blueprint: lem-sp-etale-compactification-sheaf-scalar-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- The ordinary coefficient/direct-image map, with the specified geometric counit.
It is the B-geometric adjunct of scalar/pullback reassociation followed by scalar
extension of the A-geometric counit, rather than an unspecified comparison.
Source: Stacks, Tags 03EL and 0GL6
(blueprint: lem-sp-etale-compactification-sheaf-scalar-map). -/
def compactificationOrdinaryScalarMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :
    lowerStar (ModuleCat.{u + 1} A) r ⋙ ProEtale.etaleSheafExtendScalars φ V ⟶
      ProEtale.etaleSheafExtendScalars φ W ⋙ lowerStar (ModuleCat.{u + 1} B) r :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom))

attribute [local irreducible] upperStar ProEtale.etaleSheafExtendScalars
  etaleLowerShriek openImmersionLowerShriek
  upperStarLowerStarAdjunction ProEtale.etaleSheafExtendScalarsAdjunction
  Sheaf.monoidalCategory

private theorem cached_groth (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance

attribute [local instance] cached_groth supportedHasSheafify

private def sum_scalar_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        ProEtale.etaleSheafExtendScalars φ V ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance :=
  ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)).leftAdjointUniq
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance))

private theorem compactification_support_factor
    (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e] [QuasiCompact e]
    :
    ∃ (L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
        Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ι : L ⟶ lowerStar (ModuleCat.{u + 1} A) e),
      (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (S : V.Etale),
        Function.Injective ((ι.app M).hom.app (op S))) ∧
      ∀ d : Compactification e,
        ∃ α : openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
            lowerStar (ModuleCat.{u + 1} A) d.g ≅ L,
          α.hom ≫ ι = compactificationSheafToDirectImage A d := by
  obtain ⟨L, ι, hi, hp, ho, σ, _, hσ, _, _⟩ := properSupportSheafComposition A
  refine ⟨L e, ι e, fun M S ↦ (hi _ _ e M S).1, ?_⟩
  intro d
  rcases d with ⟨Z, p, j, rfl, hpp, hj⟩
  have := hpp
  have := hj
  obtain ⟨oj, hoj⟩ := ho U Z j
  have hpi : ∀ M, IsIso ((ι p).app M) := hp Z V p
  have : IsIso (ι p) := NatIso.isIso_of_isIso_app (ι p)
  let α := Functor.isoWhiskerRight oj (lowerStar (ModuleCat.{u + 1} A) p) ≪≫
    Functor.isoWhiskerLeft (L j) (asIso (ι p)).symm ≪≫ σ U Z V j p
  refine ⟨α, ?_⟩
  apply NatTrans.ext
  funext M
  dsimp only [α, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, hσ]
  have hc : (asIso (ι p)).inv.app ((L j).obj M) ≫
      (ι p).app ((L j).obj M) = 𝟙 _ := (asIso (ι p)).inv_hom_id_app _
  rw [reassoc_of% hc, ← Functor.map_comp_assoc]
  change (lowerStar (ModuleCat.{u + 1} A) p).map
    ((oj.hom ≫ ι j).app M) ≫ _ = _
  rw [hoj]
  rfl

private theorem compactification_graph_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e] [QuasiCompact e]
    [IsLocallyNoetherian V] [CompactSpace V]
    (c : Compactification e) : IsIso (etaleCompactificationGraphMap A e c) := by
  classical
  obtain ⟨L, ι, hi, hfac⟩ := compactification_support_factor A e
  obtain ⟨Z, j, p, hj, hjq, hpf, hcomm⟩ :=
    e.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have := hj
  have := hpf
  let d : Compactification e := ⟨Z, p, j, hcomm.symm, inferInstance, hj⟩
  have := isIso_etaleCompactificationGraphMap_of_isFinite A e d
  obtain ⟨α, hα⟩ := hfac c
  obtain ⟨β, hβ⟩ := hfac d
  have heq : etaleCompactificationGraphMap A e c ≫ α.hom =
      etaleCompactificationGraphMap A e d ≫ β.hom := by
    ext M S x
    apply hi M S.unop
    have h₁ := compactSupportGraphSheafComparison_normalization A e c M
    have h₂ := compactSupportGraphSheafComparison_normalization A e d M
    have he : (etaleCompactificationGraphMap A e c).app M ≫ α.hom.app M ≫ ι.app M =
        (etaleCompactificationGraphMap A e d).app M ≫ β.hom.app M ≫ ι.app M := by
      rw [← NatTrans.comp_app, hα, h₁, ← NatTrans.comp_app, hβ, h₂]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f ↦ f.hom) he) S) x
  have : IsIso (etaleCompactificationGraphMap A e c ≫ α.hom) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ α.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem literal_scalar_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (upperStarRestrictScalarsIsoSheaf φ e).hom =
      Functor.whiskerLeft (Sheaf.restrictScalars V.smallEtaleTopology φ)
        (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance).hom ≫
      Functor.whiskerRight
        (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) e inferInstance).inv
        (Sheaf.restrictScalars U.smallEtaleTopology φ) := by
  let a := Sheaf.restrictCoextendScalarsAdj V.smallEtaleTopology φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) e
  let d := Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ
  let b' := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) e inferInstance
  let c' := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) e inferInstance
  have hadj : a.comp b' = c'.comp d := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    change ((a.comp b').unit.app M).hom.app S = ((c'.comp d).unit.app M).hom.app S
    simp only [Adjunction.comp_unit_app]
    dsimp only [a, b', c', d]
    let siteAdj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
      (inferInstance : Etale e) trivial
    let t := M.obj.map (siteAdj.counit.app S.unop).op
    change ((Sheaf.restrictCoextendScalarsAdj V.smallEtaleTopology φ).unit.app M).hom.app S ≫
        (ModuleCat.coextendScalars φ).map ((ModuleCat.restrictScalars φ).map t) =
      t ≫ ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ).unit.app
        ((localizationRestriction (ModuleCat B) e inferInstance).obj M)).hom.app _
    rw [restrictCoextendScalarsAdj_unit_app_hom_app,
      restrictCoextendScalarsAdj_unit_app_hom_app]
    exact ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).unit.naturality t).symm
  change ((a.comp b).leftAdjointUniq (c.comp d)).hom = _
  have hleft := leftUniq_whiskerLeft a b b'
  have hright := leftUniq_whiskerRight c' c d
  have hcomp := congrArg₂ (fun f g ↦ f ≫ g) hleft hright
  calc
    _ = ((a.comp b).leftAdjointUniq (a.comp b')).hom ≫
        ((c'.comp d).leftAdjointUniq (c.comp d)).hom := by
      rw [← hadj, Adjunction.leftAdjointUniq_trans]
    _ = _ := by
      refine hcomp.trans ?_
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ordinary_scalar_mate_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((compactificationOrdinaryScalarMate φ r).app M) =
      (lowerStar (ModuleCat.{u + 1} A) r).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app M) := by
  have ht := iterated_mateEquiv_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom)
  have h := unit_mateEquiv
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)
    (TwoSquare.mk _ _ _ _ (compactificationOrdinaryScalarMate φ r)) M
  change _ ≫ (mateEquiv _ _ (mateEquiv _ _
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom))).app _ = _ at h
  rw [ht] at h
  simp only [scalarSheafPullbackIso, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply, lowerStarCompRestrictScalarsIso, Iso.symm_hom,
    Iso.refl_inv, NatTrans.id_app, TwoSquare.mk, Functor.id_obj, Functor.comp_obj] at h
  erw [Category.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_open_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M ≫
      (upperStar (ModuleCat.{u + 1} A) j).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app _) ≫
      (upperStar (ModuleCat.{u + 1} A) j).map
        ((Sheaf.restrictScalars W.smallEtaleTopology φ).map
          ((openScalarExtensionZero φ j).hom.app M)) ≫
      (upperStarRestrictScalarsIsoSheaf φ j).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M ≫
      (Sheaf.restrictScalars U.smallEtaleTopology φ).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ W))
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
        (openRestrictScalarsIso φ j)) M
  have h' := congrArg (fun t ↦ t ≫ (upperStarRestrictScalarsIsoSheaf φ j).hom.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj
      ((ProEtale.etaleSheafExtendScalars φ U).obj M))) h
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] at h'
  rw [← openRestrictScalarsIso_inv_eq] at h'
  erw [Iso.hom_inv_id_app, Category.comp_id] at h'
  rw [openRestrictScalarsIso_inv_eq] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_open_to_direct
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openScalarExtensionZero φ j).hom.app M) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j).app
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) j).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M) := by
  let N := (ProEtale.etaleSheafExtendScalars φ U).obj M
  have hc := mateEquiv_counit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ j).hom) N
  have hm := underived_mate φ j
  rw [hm] at hc
  simp only [lowerStarRestrictScalarsIso, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hc
  refine openImmersionLowerShriek_lowerStar_hom_ext (ModuleCat.{u + 1} A) j
    (f₁ := (show (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M ⟶
      (lowerStar (ModuleCat.{u + 1} A) j).obj
        ((Sheaf.restrictScalars U.smallEtaleTopology φ).obj N) from
      (ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app _ ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openScalarExtensionZero φ j).hom.app M) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j).app N)))
    (f₂ := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) j).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M)) ?_
  simp only [Functor.map_comp, Category.assoc]
  calc
    _ = (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M := by
      erw [hc]
      have hn := (upperStarRestrictScalarsIsoSheaf φ j).hom.naturality
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j).app N)
      dsimp only [Functor.comp_map] at hn
      erw [reassoc_of% hn]
      rw [reassoc_of% (scalar_open_unit φ j M)]
      rw [← Functor.map_comp, ← Functor.map_comp,
        unit_map_openImmersionLowerShriekToLowerStar_app_counit,
        CategoryTheory.Functor.map_id, Category.comp_id]
    _ = _ := by
      erw [(upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).counit_naturality]
      erw [unit_map_openImmersionLowerShriekToLowerStar_app_counit_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_compactification_to_direct
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) (c : Compactification e)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((lowerStar (ModuleCat.{u + 1} A) c.g).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M)) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((compactificationOrdinaryScalarMate φ c.g).app _) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((lowerStar (ModuleCat.{u + 1} B) c.g).map
          ((openScalarExtensionZero φ c.i).hom.app M)) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((compactificationSheafToDirectImage B c).app
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    (compactificationSheafToDirectImage A c).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) e).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M) := by
  rw [reassoc_of% (ordinary_scalar_mate_unit φ c.g _)]
  simp only [compactificationSheafToDirectImage, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hc : (Sheaf.restrictScalars V.smallEtaleTopology φ).map
      ((lowerStarComp (ModuleCat.{u + 1} B) c.i c.g e c.comm).hom.app
        ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
      (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g e c.comm).hom.app
        ((Sheaf.restrictScalars U.smallEtaleTopology φ).obj
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) := rfl
  rw [hc]
  change (lowerStar (ModuleCat.{u + 1} A) c.g).map
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ c.Z).unit.app _) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).map
      ((Sheaf.restrictScalars c.Z.smallEtaleTopology φ).map
        ((openScalarExtensionZero φ c.i).hom.app M)) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).map
      ((Sheaf.restrictScalars c.Z.smallEtaleTopology φ).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) c.i).app _)) ≫ _ = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [scalar_open_to_direct φ c.i M]
  rw [Functor.map_comp, Category.assoc]
  exact congrArg ((lowerStar (ModuleCat.{u + 1} A) c.g).map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M) ≫ ·)
      ((lowerStarComp (ModuleCat.{u + 1} A) c.i c.g e c.comm).hom.naturality
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_sum_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫
      (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)) ≫
      (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
        ((Sheaf.restrictScalars V.smallEtaleTopology φ).map
          ((sum_scalar_iso φ e).hom.app M)) =
    (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M ≫
      (Sheaf.restrictScalars U.smallEtaleTopology φ).map
        ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance).unit.app _) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ V))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance)) M
  simpa only [sum_scalar_iso, Sheaf.restrictScalars, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc, Functor.comp_obj, Functor.id_obj] using h

private theorem transported_unit_app
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G H : D ⥤ C}
    (adj : F ⊣ G) (i : G ≅ H) (M : C) :
    (adj.ofNatIsoRight i).unit.app M = adj.unit.app M ≫ i.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id]

section
attribute [local semireducible] etaleLowerShriek

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem sum_unit_to_direct
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫
      (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) =
      (lowerStarUnit (ModuleCat.{u + 1} A) e).app M := by
  have hu : (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app M =
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M := by
    let i := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance
    have h₁ := transported_unit_app
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance) i M
    have h₂ := transported_unit_app
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance) i.symm M
    calc
      _ = (etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫ i.hom.app _ := h₁
      _ = ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫
          i.inv.app _) ≫ i.hom.app _ := by
        dsimp only [etaleLowerShriekUpperStarAdjunction, etaleLowerShriekAdjunction,
          etaleLowerShriek, localizationRestriction] at h₂ ⊢
        exact congrArg (fun t ↦ t ≫ i.hom.app _) h₂
      _ = _ := by
        rw [Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _
  have h := ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).homEquiv
    M ((lowerStar (ModuleCat.{u + 1} A) e).obj M)).apply_symm_apply
      ((lowerStarUnit (ModuleCat.{u + 1} A) e).app M)
  change (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app M ≫
    (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
      (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) = _ at h
  rwa [hu] at h

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_sum_to_direct
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((sum_scalar_iso φ e).hom.app M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} B) e
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M ≫
      (lowerStar (ModuleCat.{u + 1} A) e).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M) := by
  apply ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).homEquiv
    M _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  erw [reassoc_of% (scalar_sum_unit φ e M), reassoc_of% (sum_unit_to_direct A e M)]
  change (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M ≫
    (Sheaf.restrictScalars U.smallEtaleTopology φ).map
      ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance).unit.app _) ≫
    (Sheaf.restrictScalars U.smallEtaleTopology φ).map
      ((localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} B) e _)) = _
  rw [← Functor.map_comp, sum_unit_to_direct]
  erw [sheafCompose_map_lowerStarUnit_app (ModuleCat.{u + 1} B) e
    (ModuleCat.{u + 1} A) (ModuleCat.restrictScalars φ)]
  exact (lowerStarUnit (ModuleCat.{u + 1} A) e).naturality
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_graph_compat
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [QuasiCompact e] (c : Compactification e)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalars φ V).map
        ((etaleCompactificationGraphMap A e c).app M) ≫
      (compactificationOrdinaryScalarMate φ c.g).app _ ≫
      (lowerStar (ModuleCat.{u + 1} B) c.g).map
        ((openScalarExtensionZero φ c.i).hom.app M) =
    (sum_scalar_iso φ e).hom.app M ≫
      (etaleCompactificationGraphMap B e c).app
        ((ProEtale.etaleSheafExtendScalars φ U).obj M) := by
  obtain ⟨L, ι, hi, hfac⟩ := compactification_support_factor B e
  obtain ⟨α, hα⟩ := hfac c
  let N := (ProEtale.etaleSheafExtendScalars φ U).obj M
  have hmono_app (S : V.Etaleᵒᵖ) : Mono ((ι.app N).hom.app S) :=
    (ModuleCat.mono_iff_injective _).2 (hi N S.unop)
  have : Mono (ι.app N).hom := NatTrans.mono_of_mono_app _
  have hmono : Mono (ι.app N) :=
    Sheaf.Hom.mono_of_presheaf_mono V.smallEtaleTopology (ModuleCat.{u + 1} B) _
  have he : α.hom.app N ≫ ι.app N =
      (compactificationSheafToDirectImage B c).app N := by
    exact congrArg (fun t ↦ t.app N) hα
  have : Mono ((compactificationSheafToDirectImage B c).app N) := by
    rw [← he]
    have : Mono (α.hom.app N) := inferInstanceAs (Mono ((α.app N).hom))
    exact mono_comp (α.hom.app N) (ι.app N)
  apply (cancel_mono ((compactificationSheafToDirectImage B c).app N)).1
  apply ((ProEtale.etaleSheafExtendScalarsAdjunction φ V).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  erw [← (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.naturality_assoc]
  have hcomp := scalar_compactification_to_direct φ e c M
  have hpre := congrArg (fun t ↦ (etaleCompactificationGraphMap A e c).app M ≫ t) hcomp
  have ha := congrArg (fun t ↦ t ≫ (lowerStar (ModuleCat.{u + 1} A) e).map
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M))
    (compactSupportGraphSheafComparison_normalization A e c M)
  have hb := congrArg (fun t ↦
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map ((sum_scalar_iso φ e).hom.app M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map t)
    (compactSupportGraphSheafComparison_normalization B e c N)
  simp only [Functor.map_comp] at hb
  exact hpre.trans (ha.trans ((scalar_sum_to_direct φ e M).symm.trans hb.symm))

end AlgebraicGeometry.Etale
