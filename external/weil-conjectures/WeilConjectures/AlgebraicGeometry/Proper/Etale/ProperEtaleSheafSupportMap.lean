/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
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

/-! # The proper-first support map on sheaves

## References

* Stacks Project, Tags 0F7B and 0F4L
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local irreducible] lowerStar etaleLowerShriek openImmersionLowerShriek

/-- Proper support constructs a sheaf map from proper pushforward followed by etale sum
extension to any compactification, normalized by the inclusion in ordinary direct image. -/
theorem properEtaleSheafSupportMap_exists
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}}
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    (d : Compactification v) (c : Compactification (q ≫ v)) :
    ∃ τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g,
      ∀ M, τ.app M ≫ (compactificationSheafToDirectImage A c).app M =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj M) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v).hom.app M := by
  classical
  obtain ⟨L, ι, _, hp, ho, σ, _, hσ, _, _⟩ := properSupportSheafComposition A
  have hproper {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g] : IsIso (ι g) := by
    have : ∀ M, IsIso ((ι g).app M) := hp V W g
    exact NatIso.isIso_of_isIso_app _
  have hfac {V W : Scheme.{u}} (g : V ⟶ W) [IsSeparated g]
      [LocallyOfFiniteType g] (d : Compactification g) :
      ∃ α : openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
          lowerStar (ModuleCat.{u + 1} A) d.g ≅ L g,
        α.hom ≫ ι g = compactificationSheafToDirectImage A d := by
    rcases d with ⟨Z, p, j, rfl, hpp, hj⟩
    have := hpp
    have := hj
    obtain ⟨oj, hoj⟩ := ho V Z j
    have := hproper p
    let α := Functor.isoWhiskerRight oj (lowerStar (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft (L j) (asIso (ι p)).symm ≪≫ σ V Z W j p
    refine ⟨α, ?_⟩
    apply NatTrans.ext
    funext M
    dsimp only [α, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    rw [Category.assoc, Category.assoc, hσ]
    have hcancel : (asIso (ι p)).inv.app ((L j).obj M) ≫
        (ι p).app ((L j).obj M) = 𝟙 _ := (asIso (ι p)).inv_hom_id_app _
    rw [reassoc_of% hcancel, ← Functor.map_comp_assoc]
    change (lowerStar (ModuleCat.{u + 1} A) p).map
      ((oj.hom ≫ ι j).app M) ≫ _ = _
    rw [hoj]
    rfl
  have := hproper q
  obtain ⟨α, hα⟩ := hfac v d
  obtain ⟨β, hβ⟩ := hfac (q ≫ v) c
  let a := etaleCompactificationGraphMap A v d ≫ α.hom
  have hn (M) : a.app M ≫ (ι v).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v M := by
    simp only [a, Category.assoc, ← NatTrans.comp_app, hα]
    exact compactSupportGraphSheafComparison_normalization A v d M
  let τ := Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} A) q) a ≫
    Functor.whiskerRight (asIso (ι q)).inv (L v) ≫ (σ W V Y q v).hom ≫ β.inv
  refine ⟨τ, fun M ↦ ?_⟩
  have hb := congr_app hβ M
  simp only [NatTrans.comp_app] at hb
  simp only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [← hb, Iso.inv_hom_id_app_assoc, hσ]
  have nv := (ι v).naturality ((asIso (ι q)).inv.app M)
  rw [reassoc_of% nv, ← (lowerStar (ModuleCat.{u + 1} A) v).map_comp_assoc]
  change a.app _ ≫ (ι v).app _ ≫
    (lowerStar (ModuleCat.{u + 1} A) v).map
      ((asIso (ι q)).inv.app M ≫ (asIso (ι q)).hom.app M) ≫ _ = _
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hn]

end AlgebraicGeometry.Etale
