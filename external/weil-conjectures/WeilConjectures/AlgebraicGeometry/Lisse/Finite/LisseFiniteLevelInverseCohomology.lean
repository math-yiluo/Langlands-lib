/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Over
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
public import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
public import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
public import Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Precoverage.Generates
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Basic.Finite.Prod
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsModel
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullback
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-! # Cohomology of the inverse finite scalar realization

## References

* Stacks Project, Modules on Sites, exactness of inverse image and constants (Tags 03DC and 093J)
* Stacks Project, Tag 099Y
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The inverse fixed realization of the actual pullback has the bounds of its local
algebraic models and lisse pro-etale cohomology. This is a cohomology assertion only;
no etale derived model or comparison of derived objects is asserted. -/
theorem lisse_finite_level_inverse_realization_cohomology
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj E))
    (hfinite : ∀ q : ℤ, Module.Finite (lisseTowerEtaleRing d n)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) q).obj E))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    let K := (lisseTowerFixedRealization (U.hom ≫ g) d n).asEquivalence.inverse.obj
      ((adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N)
    (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∀ q : ℤ, IsLisseProEtaleFixedModuleSheaf U.left (lisseTowerEtaleRing d n)
        ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  classical
  let B := lisseTowerEtaleRing d n
  let F := lisseTowerFixedRealization (U.hom ≫ g) d n
  let N₀ := (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N
  let K := F.asEquivalence.inverse.obj N₀
  change (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧ _
  let e : F.obj K ≅ N₀ := F.asEquivalence.counitIso.app N₀
  obtain ⟨T, hT, hm⟩ := hmodels
  obtain ⟨P, hP, hPT⟩ := ProEt.mem_topology_iff.mp hT
  obtain ⟨ι, W, w, rfl⟩ := P.exists_eq_ofArrows
  have hg : Presieve.ofArrows (fun i ↦ (W i).left) (fun i ↦ (w i).left) ∈
      Scheme.proetalePrecoverage U.left := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
    exact hP
  have hweak (i : ι) : WeaklyEtale (w i).left :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ hg ⟨i⟩
  let (i : ι) : WeaklyEtale (w i).left := hweak i
  have localModel (i : ι) : Nonempty (
      (ProEtale.upperStar (ModuleCat.{u + 1} B) (w i).left).mapDerivedCategory.obj K ≅
      (localProEtaleComparison (w i).left B).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E)) := by
    obtain ⟨em⟩ := hm (W i) (w i) (hPT _ _ ⟨i⟩)
    let a := (w i).left
    let b := U.hom ≫ g
    have hab : a ≫ b = (W i).hom ≫ g := by
      have h := (w i).w
      change (w i).left ≫ U.hom = (W i).hom ≫ 𝟙 Y at h
      erw [Category.comp_id] at h
      simpa only [a, b, Category.assoc] using congrArg (fun t ↦ t ≫ g) h
    let F' := lisseTowerFixedRealization ((W i).hom ≫ g) d n
    let C₀ := (normalizationConstant U.left.smallEtaleTopology).obj E
    let K₀ := (localProEtaleComparison a B).obj C₀
    obtain ⟨models⟩ :=
      lisseTower_localized_constants_model ((W i).hom ≫ g) a (𝟙 (W i).left) d
    let idD := Functor.mapDerivedCategoryNatIso
        (ProEtale.upperStarId (ModuleCat.{u + 1} B) (W i).left) ≪≫
      Functor.mapDerivedCategoryIdIso _
    have model : F'.obj K₀ ≅
        (constantAdicQuotientRealization ((W i).hom ≫ g) d n).obj E :=
      F'.mapIso (idD.app K₀).symm ≪≫ models n E
    let R := (pbcAdicRings X d).obj (op n)
    let RT := (adicTowerInverseImage b).obj R
    let RZ := (adicTowerInverseImage (a ≫ b)).obj R
    let c := (proEtaleRingInverseImageComp a b).symm.app R
    let Q := proEtaleRingModulePullback a RT RZ c
    have hc : Iso.refl RZ = proEtaleRingCompositeCoefficients a b R RT RZ
        (Iso.refl RT) c := by
      apply Iso.ext
      change 𝟙 RZ = (proEtaleRingInverseImageComp a b).hom.app R ≫
        (adicTowerInverseImage a).map (𝟙 RT) ≫
          (proEtaleRingInverseImageComp a b).inv.app R
      erw [(adicTowerInverseImage a).map_id RT, Category.id_comp]
      exact (Iso.hom_inv_id_app (proEtaleRingInverseImageComp a b) R).symm
    let comp := (proEtaleCanonicalPullbackComposition_existsUnique a b R RT RZ
      (Iso.refl RT) c (Iso.refl RZ) hc).exists.choose
    let sq := (lisseTower_fixed_sheaf_pullback a b d n).some
    let dsq : (ProEtale.upperStar (ModuleCat.{u + 1} B) a).mapDerivedCategory ⋙
          lisseTowerFixedRealization (a ≫ b) d n ≅
        lisseTowerFixedRealization b d n ⋙ Q.mapDerivedCategory :=
      Functor.isoWhiskerLeft _ (lisseTowerFixedRealizationIso (a ≫ b) d n).symm ≪≫
        Functor.mapDerivedCategorySquareIso sq ≪≫
        Functor.isoWhiskerRight (lisseTowerFixedRealizationIso b d n) Q.mapDerivedCategory
    have actual : (lisseTowerFixedRealization (a ≫ b) d n).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} B) a).mapDerivedCategory.obj K) ≅
        (adicTowerPullback (a ≫ b) R).obj N :=
      dsq.app K ≪≫ Q.mapDerivedCategory.mapIso e ≪≫ (comp.app N).symm
    rw [hab] at actual
    exact ⟨F'.preimageIso (actual ≪≫ em.symm ≪≫ model.symm)⟩
  have cohomModel (q : ℤ) (i : ι) : Nonempty (
      (ProEtale.upperStar (ModuleCat.{u + 1} B) (w i).left).obj
        ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (constantSheaf (ProEt.topology (W i).left) (ModuleCat.{u + 1} B)).obj
        ((DerivedCategory.homologyFunctor _ q).obj E)) := by
    obtain ⟨em⟩ := localModel i
    let R := ProEtale.upperStar (ModuleCat.{u + 1} B) (w i).left
    let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) U.left
    let H := constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} B)
    let comparisonConstants : H ⋙ C ≅
        constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} B) :=
      Functor.isoWhiskerLeft H
        (Functor.sheafPullbackConstruction.sheafPullbackIso (toProEt U.left)
          (ModuleCat.{u + 1} B) U.left.smallEtaleTopology (ProEt.topology U.left)).symm ≪≫
      (toProEt U.left).constantSheafsheafPullbackIso (ModuleCat.{u + 1} B)
        U.left.smallEtaleTopology (ProEt.topology U.left)
        (Etale.isTerminalMkId U.left) (ProEt.isTerminalMkId U.left)
    let pullConstants : constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} B) ⋙ R ≅
        constantSheaf (ProEt.topology (W i).left) (ModuleCat.{u + 1} B) :=
      Functor.isoWhiskerLeft _
        (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange (w i).left)
          (ModuleCat.{u + 1} B) (ProEt.topology U.left) (ProEt.topology (W i).left)).symm ≪≫
      (proEtaleBaseChange (w i).left).constantSheafsheafPullbackIso (ModuleCat.{u + 1} B)
        (ProEt.topology U.left) (ProEt.topology (W i).left) (ProEt.isTerminalMkId U.left)
        ((ProEt.isTerminalMkId U.left).isTerminalObj (proEtaleBaseChange (w i).left) _)
    exact ⟨(R.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso em ≪≫
      ((R.mapDerivedCategoryHomologyFunctorIso q).app
        (C.mapDerivedCategory.obj (H.mapDerivedCategory.obj E))).symm ≪≫
      R.mapIso (((C.mapDerivedCategoryHomologyFunctorIso q).app
        (H.mapDerivedCategory.obj E)).symm) ≪≫
      R.mapIso (C.mapIso (((H.mapDerivedCategoryHomologyFunctorIso q).app E).symm)) ≪≫
      R.mapIso (comparisonConstants.app _) ≪≫ pullConstants.app _⟩
  have finiteModels (q : ℤ) : ∃ (ι : Type (u + 1)) (V : ι → Scheme.{u})
      (f : ∀ i, V i ⟶ U.left),
      Presieve.ofArrows V f ∈ Scheme.proetalePrecoverage U.left ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} B, Finite M ∧
          Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} B) (f i)).obj
            ((DerivedCategory.homologyFunctor _ q).obj K) ≅
              (constantSheaf (ProEt.topology (V i)) (ModuleCat.{u + 1} B)).obj M) := by
    have := hfinite q
    exact ⟨ι, fun i ↦ (W i).left, fun i ↦ (w i).left, hg,
      fun i ↦ ⟨_, Module.finite_of_finite B, cohomModel q i⟩⟩
  constructor
  · obtain ⟨a, b, hab⟩ := hbounded
    refine ⟨a, b, fun q hq ↦ ?_⟩
    let H := (DerivedCategory.homologyFunctor _ q).obj K
    have hz (i : ι) : IsZero
        ((ProEtale.upperStar (ModuleCat.{u + 1} B) (w i).left).obj H) := by
      obtain ⟨ec⟩ := cohomModel q i
      exact ((constantSheaf (ProEt.topology (W i).left)
        (ModuleCat.{u + 1} B)).map_isZero (hab q hq)).of_iso ec
    have : IsIso (0 : H ⟶ 0) := by
      refine ProEtale.isIso_of_isIso_localizationRestriction
        (ModuleCat.{u + 1} B) (0 : H ⟶ 0) (fun i ↦ (w i).left) hg fun i ↦ ?_
      let e := ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) (w i).left inferInstance
      exact isIso_of_source_target_iso_zero _ ((hz i).of_iso (e.app H).symm).isoZero
        (((ProEtale.upperStar (ModuleCat.{u + 1} B) (w i).left).map_isZero
          (isZero_zero _)).of_iso (e.app 0).symm).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : H ⟶ 0))
  · intro q
    refine ⟨?_, ?_⟩
    · obtain ⟨I, V, f, hf, h⟩ := ProEtale.finiteModels_over B _ (finiteModels q)
      exact ⟨I, V, f, hf, fun i ↦ by
        obtain ⟨M, _, he⟩ := h i
        exact ⟨M, he⟩⟩
    · intro Ω hΩ hΩalg x
      exact ProEtale.finite_geometricStalk_of_finite_models B _ (finiteModels q) Ω x

end AlgebraicGeometry.Scheme
