/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Basic

public import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
public import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
public import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
public import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
public import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
public import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
public import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
public import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.Compactification.RefinementCategory

import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitComposition
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitIdentity
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportNestedSummands
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitRefinement
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFiniteCompactificationSheafIso
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Quasi-finite compact support is exact

## References

* Stacks Project, More on Étale Cohomology, Tag 0GKM, with Tags 0F4Y, 0F50, 0F7J and 0F5F
* Stacks Project, More on Étale Cohomology, Tags 0GKM, 0F4Y, 0F50, 0F7J and 0F5F
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Proper-support direct image for a separated quasi-finite finite-type map is exact and
agrees on all unbounded complexes with every compactification construction. The comparison
family is compatible with canonical compactification changes, composition, étale sum extension,
and identity normalization. Identity comparisons agree with the three comparison families
whenever their compactifications (with target scheme and morphism) coincide.
-/
theorem quasifiniteCompactSupportExact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (hhq : h.IsQuasiFinite) (ehq : e.IsQuasiFinite) :
    ∃ (L : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ∃ (ι : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        L f ⟶ lowerStar (ModuleCat.{u + 1} A) f),
      ∃ (o : ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
          (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f],
          etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅ L f),
      ∃ (hA : (L h).Additive),
      ∃ (hL : PreservesFiniteLimits (L h)),
      ∃ (hC : PreservesFiniteColimits (L h)),
      ∃ (eA : (L e).Additive),
      ∃ (eL : PreservesFiniteLimits (L e)),
      ∃ (eC : PreservesFiniteColimits (L e)),
      ∃ (heA : (L (h ≫ e)).Additive),
      ∃ (heL : PreservesFiniteLimits (L (h ≫ e))),
      ∃ (heC : PreservesFiniteColimits (L (h ≫ e))),
      ∃ (c_h : ∀ c : Compactification h,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC),
      ∃ (c_e : ∀ c : Compactification e,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L e) eA eL eC),
      ∃ (c_he : ∀ c : Compactification (h ≫ e),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (h ≫ e)) heA heL heC),
      ∃ (idA : ∀ (X : Scheme.{u}) [IsNoetherian X], (L (𝟙 X)).Additive),
      ∃ (idL : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteLimits (L (𝟙 X))),
      ∃ (idC : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteColimits (L (𝟙 X))),
      ∃ (c_id : ∀ (X : Scheme.{u}) [IsNoetherian X] (c : Compactification (𝟙 X)),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (𝟙 X)) (idA X) (idL X) (idC X)),
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (V : Y.Etale),
        Function.Injective (((ι f).app F).hom.app (Opposite.op V)) ∧
        (∀ s : F.obj.obj (Opposite.op
            ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)),
          (∃ t, (((ι f).app F).hom.app (Opposite.op V)) t = s) ↔
          ∃ T₀ : TopologicalSpace.Closeds
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left,
            (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
              (v₀ : Spec (.of Ω) ⟶
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left),
              v₀ default ∈ T₀ ↔
                (Scheme.pointSmallEtale
                  (v₀ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom)).toPresheafFiber
                    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
                    (Over.homMk v₀) F.obj s ≠ 0) ∧
            IsProper ((Scheme.IdealSheafData.vanishingIdeal T₀).subschemeι ≫
              pullback.fst V.hom f))) ∧
      (∀ c d : Compactification h,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_h d).hom = (c_h c).hom) ∧
      (∀ c d : Compactification e,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_e d).hom = (c_e c).hom) ∧
      (∀ c d : Compactification (h ≫ e),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_he d).hom = (c_he c).hom) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X] (c d : Compactification (𝟙 X)),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_id X d).hom = (c_id X c).hom) ∧
      (∀ (c : Compactification h) (d : Compactification (𝟙 V)),
        (⟨T, h, c⟩ : Σ Y : Scheme.{u}, Σ f : V ⟶ Y, Compactification f) =
          ⟨V, 𝟙 V, d⟩ → HEq (c_h c) (c_id V d)) ∧
      (∀ (c : Compactification e) (d : Compactification (𝟙 T)),
        (⟨B, e, c⟩ : Σ Y : Scheme.{u}, Σ f : T ⟶ Y, Compactification f) =
          ⟨T, 𝟙 T, d⟩ → HEq (c_e c) (c_id T d)) ∧
      (∀ (c : Compactification (h ≫ e)) (d : Compactification (𝟙 V)),
        (⟨B, h ≫ e, c⟩ : Σ Y : Scheme.{u}, Σ f : V ⟶ Y, Compactification f) =
          ⟨V, 𝟙 V, d⟩ → HEq (c_he c) (c_id V d)) ∧
      (∃ σ : L h ⋙ L e ≅ L (h ≫ e),
        (∀ F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
          σ.hom.app F ≫ (ι (h ≫ e)).app F =
            (ι e).app ((L h).obj F) ≫
              (lowerStar (ModuleCat.{u + 1} A) e).map ((ι h).app F) ≫
              (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app F) ∧
        ((unboundedEtaleLowerShriekCompIso A h e ≪≫
          (rightDerivedLowerShriekIso A
            (HasCompactification.compactification (h ≫ e))).symm ≪≫
          c_he (HasCompactification.compactification (h ≫ e))) =
          (Functor.isoWhiskerRight
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification h)).symm ≪≫
              c_h (HasCompactification.compactification h))
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e) ≪≫
          Functor.isoWhiskerLeft
            (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC)
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification e)).symm ≪≫
              c_e (HasCompactification.compactification e)) ≪≫
          Functor.mapDerivedCategoryCompIso (L h) (L e) ≪≫
          Functor.mapDerivedCategoryNatIso σ)) ∧
        (∀ [Etale h] [Etale e]
          (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale),
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) h).unit.app F).hom.app
              (Opposite.op W) ≫
            ((o h).hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app
              ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((o e).hom.app ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) ≫
            (σ.hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) =
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
              (h ≫ e)).unit.app F).hom.app (Opposite.op W) ≫
            ((o (h ≫ e)).hom.app F).hom.app
              (Opposite.op
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale (h ≫ e))).obj W)) ≫
            ((L (h ≫ e)).obj F).obj.map
              ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale h)
                (inferInstance : Etale e)).inv.app W).op)) ∧
      (∀ (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (o f).hom.app F ≫ (ι f).app F =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f F) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X], ∃ i_id : L (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)),
        i_id.hom = ι (𝟙 X) ≫ (lowerStarId (ModuleCat.{u + 1} A) X).hom ∧
        (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫
          c_id X (Compactification.ofIsProper (𝟙 X)) ≪≫
          @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
            (F := L (𝟙 X))
            (G := 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (idA X) (by infer_instance) (idL X) (idC X)
            (by infer_instance) (by infer_instance) i_id ≪≫
          Functor.mapDerivedCategoryIdIso _ =
          unboundedEtaleLowerShriekId A X) := by
  classical
  obtain ⟨L, ι, hi, hp, ho, σ, _, hσ, _, _⟩ := properSupportSheafComposition A
  have hproper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsIso (ι f) := by
    have : ∀ F, IsIso ((ι f).app F) := hp X Y f
    exact NatIso.isIso_of_isIso_app (ι f)
  have hfac {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
      [LocallyOfFiniteType f] (c : Compactification f) :
      ∃ α : openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
          lowerStar (ModuleCat.{u + 1} A) c.g ≅ L f,
        α.hom ≫ ι f = compactificationSheafToDirectImage A c := by
    rcases c with ⟨Z, p, j, rfl, hpp, hj⟩
    have := hpp
    have := hj
    obtain ⟨oj, hoj⟩ := ho X Z j
    have := hproper p
    let α := Functor.isoWhiskerRight oj (lowerStar (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft (L j) (asIso (ι p)).symm ≪≫ σ X Z Y j p
    refine ⟨α, ?_⟩
    apply NatTrans.ext
    funext F
    dsimp only [α, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    rw [Category.assoc, Category.assoc, hσ]
    have hcancel : (asIso (ι p)).inv.app ((L j).obj F) ≫
        (ι p).app ((L j).obj F) = 𝟙 _ := (asIso (ι p)).inv_hom_id_app _
    rw [reassoc_of% hcancel]
    rw [← Functor.map_comp_assoc]
    change (lowerStar (ModuleCat.{u + 1} A) p).map
      ((oj.hom ≫ ι j).app F) ≫ _ = _
    rw [hoj]
    rfl
  have hexact {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] :
      (L f).Additive ∧ PreservesFiniteLimits (L f) ∧ PreservesFiniteColimits (L f) := by
    obtain ⟨Z, j, p, hj, hjq, hpf, hcomm⟩ :=
      f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
    have := hj
    have := hpf
    let c : Compactification f := ⟨Z, p, j, hcomm.symm, inferInstance, hj⟩
    obtain ⟨α, _⟩ := hfac f c
    have : (L f).Additive := Functor.additive_of_iso α
    exact ⟨this, preservesFiniteLimits_of_natIso α, preservesFiniteColimits_of_natIso α⟩
  let a {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
      [LocallyOfFiniteType f] (c : Compactification f) :=
    (Classical.choose (hfac f c)).symm
  have ha {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
      [LocallyOfFiniteType f] (c : Compactification f) :
      (a f c).hom ≫ compactificationSheafToDirectImage A c = ι f := by
    rw [← Classical.choose_spec (hfac f c)]
    exact (a f c).hom_inv_id_assoc _
  let DA {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] : (L f).Additive := (hexact f).1
  let DL {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] : PreservesFiniteLimits (L f) := (hexact f).2.1
  let DC {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] : PreservesFiniteColimits (L f) := (hexact f).2.2
  let δ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] (c : Compactification f) :=
    @exactCompactificationUnit A _ X Y f c (L f) (DA f) (DL f) (DC f) (a f c)
  have hδ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] (c d : Compactification f) :
      δ f c ≫ (rightDerivedLowerShriekOfCompactificationIso A c d).hom = δ f d := by
    exact @exactCompactificationUnit_refinement A _ _ X Y _ _ f _ _ _
      (L f) (DA f) (DL f) (DC f) c d (a f c) (a f d)
      ((ha f c).trans (ha f d).symm)
  have hδiso {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] (c : Compactification f) : IsIso (δ f c) := by
    obtain ⟨Z, j, p, hj, hjq, hpf, hcomm⟩ :=
      f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
    have := hj
    have := hpf
    let d : Compactification f := ⟨Z, p, j, hcomm.symm, inferInstance, hj⟩
    have hd : IsIso (δ f d) :=
      @isIso_exactCompactificationUnit_of_isFinite A _ X Y f d (L f)
        (DA f) (DL f) (DC f) (a f d) hpf
    rw [← hδ f d c]
    infer_instance
  let C {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] (c : Compactification f) :=
    letI := hδiso f c
    (asIso (δ f c)).symm
  have hC {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [LocallyQuasiFinite f] (c d : Compactification f) :
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
        (C f d).hom = (C f c).hom := by
    let := hδiso f c
    let := hδiso f d
    change _ ≫ inv (δ f d) = inv (δ f c)
    apply (cancel_epi (δ f c)).1
    rw [← Category.assoc, hδ, IsIso.hom_inv_id, IsIso.hom_inv_id]
  have : LocallyQuasiFinite h := (Scheme.Hom.isQuasiFinite_iff h).mp hhq |>.1
  have : LocallyQuasiFinite e := (Scheme.Hom.isQuasiFinite_iff e).mp ehq |>.1
  have hoetale {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f] :
      ∃ o : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅ L f,
        ∀ M, o.hom.app M ≫ (ι f).app M =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M := by
    obtain ⟨Z, j, p, hj, hjq, hpf, hcomm⟩ :=
      f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
    have := hj
    have := hpf
    let c : Compactification f := ⟨Z, p, j, hcomm.symm, inferInstance, hj⟩
    have := isIso_etaleCompactificationGraphMap_of_isFinite A f c
    obtain ⟨α, hα⟩ := hfac f c
    refine ⟨asIso (etaleCompactificationGraphMap A f c) ≪≫ α, ?_⟩
    intro M
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    change (etaleCompactificationGraphMap A f c).app M ≫
      (α.hom.app M ≫ (ι f).app M) = _
    rw [← NatTrans.comp_app, hα]
    exact compactSupportGraphSheafComparison_normalization A f c M
  let o {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f] :=
    Classical.choose (hoetale f)
  have honorm {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f] (M) :
      (o f).hom.app M ≫ (ι f).app M =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M :=
    Classical.choose_spec (hoetale f) M
  refine ⟨L, ι, o, DA h, DL h, DC h, DA e, DL e, DC e,
    DA (h ≫ e), DL (h ≫ e), DC (h ≫ e), C h, C e, C (h ≫ e),
    fun X _ => DA (𝟙 X), fun X _ => DL (𝟙 X), fun X _ => DC (𝟙 X),
    fun X _ => C (𝟙 X), hi, hC h, hC e, hC (h ≫ e),
    fun X _ => hC (𝟙 X), ?_, ?_, ?_, ?_, @honorm, ?_⟩
  · intro c d hcd
    have ht := congrArg Sigma.fst hcd
    dsimp only at ht
    subst T
    have hf : h = 𝟙 V := (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hcd).2)).1
    subst h
    have hc : c = d := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hcd).2)).2
    subst c
    rfl
  · intro c d hcd
    have ht := congrArg Sigma.fst hcd
    dsimp only at ht
    subst B
    have hf : e = 𝟙 T := (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hcd).2)).1
    subst e
    have hc : c = d := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hcd).2)).2
    subst c
    rfl
  · intro c d hcd
    have ht := congrArg Sigma.fst hcd
    dsimp only at ht
    subst B
    have hf : h ≫ e = 𝟙 V := (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hcd).2)).1
    have hc : HEq c d := (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hcd).2)).2
    have hcongr (f g : V ⟶ V)
        [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
        [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [LocallyQuasiFinite g]
        (p : f = g) (c : Compactification f) (d : Compactification g) (q : HEq c d) :
        HEq (C f c) (C g d) := by
      subst g
      cases eq_of_heq q
      rfl
    exact hcongr (h ≫ e) (𝟙 V) hf c d hc
  · refine ⟨σ V T B h e, hσ V T B h e, ?_, ?_⟩
    · let := DA h
      let := DL h
      let := DC h
      let := DA e
      let := DL e
      let := DC e
      let := DA (h ≫ e)
      let := DL (h ≫ e)
      let := DC (h ≫ e)
      exact exactCompactificationUnit_composition A h e (L h) (L e) (L (h ≫ e))
        (ι h) (ι e) (ι (h ≫ e)) (a h) (a e) (a (h ≫ e))
        (ha h) (ha e) (ha (h ≫ e)) (C h) (C e) (C (h ≫ e))
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (σ V T B h e) (hσ V T B h e)
    · intro _ _ M W
      exact etaleSupportNestedSummands A h e (L h) (L e) (L (h ≫ e))
        (ι h) (ι e) (ι (h ≫ e)) (fun M W => (hi V B (h ≫ e) M W).1)
        (o h) (o e) (o (h ≫ e)) (honorm h) (honorm e) (honorm (h ≫ e))
        (σ V T B h e) (hσ V T B h e) M W
  · intro X _
    have := hproper (𝟙 X)
    refine ⟨asIso (ι (𝟙 X)) ≪≫ lowerStarId (ModuleCat.{u + 1} A) X, rfl, ?_⟩
    let := DA (𝟙 X)
    let := DL (𝟙 X)
    let := DC (𝟙 X)
    exact exactCompactificationUnit_identity A X (L (𝟙 X)) (ι (𝟙 X))
      (a (𝟙 X) (Compactification.ofIsProper (𝟙 X)))
      (ha (𝟙 X) (Compactification.ofIsProper (𝟙 X)))
      (C (𝟙 X) (Compactification.ofIsProper (𝟙 X))) rfl
end AlgebraicGeometry.Etale
