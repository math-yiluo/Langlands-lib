/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDerivedOriginPresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons

/-! # Core data for a single finite quotient étale origin

## References

* Stacks Project, Tags 09AL and 09B1
* Stacks Project, Tags 093I and 03CY
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

namespace FiniteQuotientOriginProof

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem inverseImage_additive {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g R).Additive :=
  (proEtaleModuleInverseImageAdjunction g R).left_adjoint_additive

private theorem inverseImage_limits {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleModuleInverseImage g R) :=
  proEtaleModuleInverseImage_preservesFiniteLimits g R

private theorem inverseImage_colimits {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleModuleInverseImage g R) := by
  have : PreservesColimitsOfSize.{0, 0} (proEtaleModuleInverseImage g R) :=
    (proEtaleModuleInverseImageAdjunction g R).leftAdjoint_preservesColimits
  infer_instance

attribute [local instance] inverseImage_additive inverseImage_limits inverseImage_colimits

private theorem scalar_additive (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    (scalarRestriction X B).Additive where
  map_add := by intros; ext U x; rfl

private theorem relative_additive {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] : (relativeRestriction g B).Additive where
  map_add := by intros; ext U x; rfl

private theorem scalar_equivalence (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    (scalarRestriction X B).IsEquivalence := scalarRestriction_equivalence X B

private theorem relative_equivalence {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] : (relativeRestriction g B).IsEquivalence := by
  let E := proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso (constantCoefficients g B))
  change (E.inverse ⋙ scalarRestriction Y B).IsEquivalence
  have := scalar_equivalence Y B
  infer_instance

attribute [local instance] scalar_additive relative_additive scalar_equivalence relative_equivalence

private def fixedPullbackIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (N : DerivedCategory (pbcModules X (adicLisseConstantRing X B))) :
    (relativeRestriction g B).mapDerivedCategory.obj
        ((adicTowerPullback g (adicLisseConstantRing X B)).obj N) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.obj
        ((scalarRestriction X B).mapDerivedCategory.obj N) := by
  let P := proEtaleModuleInverseImage g (adicLisseConstantRing X B)
  let e := (proEtaleModuleInverseImageAdjunction g (adicLisseConstantRing X B)).leftAdjointUniq
    (proEtaleRingModuleAdjunction g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _))
  exact (relativeRestriction g B).mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryNatIso e).app N).symm ≪≫
    (Functor.mapDerivedCategoryCompIso P (relativeRestriction g B)).app N ≪≫
    (Functor.mapDerivedCategoryNatIso (relativeEncoding g B)).app N ≪≫
    ((Functor.mapDerivedCategoryCompIso (scalarRestriction X B)
      (ProEtale.upperStar (ModuleCat.{u + 1} B) g)).app N).symm

private def fixedHomologyIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))) (q : ℤ) :
    (relativeRestriction g (A ⧸ d.ideal ^ (n + 1))).obj
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj K))) ≅
      (DerivedCategory.homologyFunctor _ q).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) g).mapDerivedCategory.obj
          ((scalarRestriction X (A ⧸ d.ideal ^ (n + 1))).mapDerivedCategory.obj ((pbcDerivedRestrict
              (pbcLevelConstantComparison X d n).hom).obj K))) := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let N := (pbcDerivedRestrict (pbcLevelConstantComparison X d n).hom).obj K
  let e := pbcLevelConstantComparison X d n
  let c := proEtaleRingRestrictionDerivedPullback g _ _
    ((adicTowerInverseImage g).obj _) ((adicTowerInverseImage g).obj _)
    e.hom ((adicTowerInverseImage g).map e.hom) (Iso.refl _) (Iso.refl _) (by simp)
  let eH := (DerivedCategory.homologyFunctor _ q).mapIso (c.app K).symm ≪≫
    (((pbcRestrict ((adicTowerInverseImage g).map e.hom)).mapDerivedCategoryHomologyFunctorIso
      q).app ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj K)).symm
  exact (relativeRestriction g B).mapIso eH.symm ≪≫
    ((relativeRestriction g B).mapDerivedCategoryHomologyFunctorIso q).app
      ((adicTowerPullback g (adicLisseConstantRing X B)).obj N) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso (fixedPullbackIso g B N)

private theorem scalar_lisse {X : Scheme.{u}}
    {B C : Type (u + 1)} [CommRing B] [CommRing C] [Finite B] [Finite C]
    (r : C →+* B) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars X.smallEtaleTopology r).obj F) := by
  obtain ⟨d, hd⟩ := (finite_locally_constant_module_values_iff F).1.mpr hF
  let T := Sheaf.restrictScalars X.smallEtaleTopology r
  let d' : LocallyConstantDatum (T.obj F) :=
    { cover := d.cover
      isConstant i := by
        change ((Sheaf.restrictScalars
          (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i)) r).obj
            (F.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
        have := d.isConstant i
        infer_instance }
  apply (finite_locally_constant_module_values_iff (T.obj F)).1.mp
  refine ⟨d', fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hd i
  have : Finite M := hM
  let J := X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i)
  exact ⟨(ModuleCat.restrictScalars r).obj M, hM,
    ⟨(Sheaf.restrictScalars J r).mapIso e ≪≫
      (constantCommuteCompose J (ModuleCat.restrictScalars r)).app M⟩⟩

end FiniteQuotientOriginProof

/-- The fixed-coefficient encoding of modules over the constant ring sheaf.
Its underlying module-valued sheaf is restriction along the constant-section map. -/
def finiteQuotientOriginEncoding (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    pbcModules X (adicLisseConstantRing X B) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars (adicLisseConstantUnit X B)).obj M.val
    let F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology X) F
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars (adicLisseConstantUnit X B)).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

instance finiteQuotientOriginEncoding_additive (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] : (finiteQuotientOriginEncoding X B).Additive where
  map_add := by intros; ext U x; rfl

instance finiteQuotientOriginEncoding_equivalence (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] : (finiteQuotientOriginEncoding X B).IsEquivalence :=
  FiniteQuotientOriginProof.scalar_equivalence X B

/-- The actual fixed-coefficient realization of the pullback of a quotient complex. -/
def finiteQuotientOriginPullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  pbcDerivedRestrict (pbcLevelConstantComparison X d n).hom ⋙
    (finiteQuotientOriginEncoding X (A ⧸ d.ideal ^ (n + 1))).mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) g).mapDerivedCategory

/-- The descended level, its actual comparison with the pullback of `K`, and local
finiteness data, before conditional transport. The comparison uses the fixed
`A/I^(n+1)` coefficient encoding after restriction from the completion quotient.
-/
structure LisseFiniteQuotientEtaleOriginCore
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (V : Y.Etale) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj level)
  vanishing : ∀ q : ℤ,
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj level)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj K)))
  comparison : Nonempty
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)))
        V.left).mapDerivedCategory.obj
      ((Sheaf.restrictScalars V.left.smallEtaleTopology
        (constantAdicQuotientMap d.ideal n)).mapDerivedCategory.obj level) ≅
      (finiteQuotientOriginPullback (V.hom ≫ g) d n).obj K)

attribute [local instance] FiniteQuotientOriginProof.scalar_additive
  FiniteQuotientOriginProof.relative_additive FiniteQuotientOriginProof.scalar_equivalence
  FiniteQuotientOriginProof.relative_equivalence

open FiniteQuotientOriginProof in
/-- Descend the level, vanishing and finite lisse data of one quotient. -/
theorem lisse_finite_quotient_etale_origin_core
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hlisse : ∀ q : ℤ,
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj K))))
    (V : Y.Etale) :
    Nonempty (LisseFiniteQuotientEtaleOriginCore X Y g d n K V) := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let C := AdicCompletion d.ideal A ⧸
    (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)
  have : Finite B := d.quotientFinite n
  let eBC : B ≃+* C := RingEquiv.ofBijective (constantAdicQuotientMap d.ideal n)
    (quotient_map_bijective d.ideal d.finitelyGenerated n)
  have : Finite C := Finite.of_surjective eBC eBC.surjective
  let R := pbcRestrict (pbcLevelConstantComparison X d n).hom
  let S := scalarRestriction X B
  let N := R.mapDerivedCategory.obj K
  let J := S.mapDerivedCategory.obj N
  let P := (ProEtale.upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.obj J
  have hP (q : ℤ) : ProEtale.IsFiniteLocallyConstant B
      ((DerivedCategory.homologyFunctor _ q).obj P) := by
    exact ProEtale.isFiniteLocallyConstant_of_iso
      (FiniteQuotientOriginProof.fixedHomologyIso g d n K q)
      ((fixedFiniteModels_iff Y B _).mp ((relativeFinite_iff g B _).mp (hlisse q)))
  have hz (q : ℤ) (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj P) :=
    (ProEtale.upperStar (ModuleCat.{u + 1} B) g).isZero_homologyFunctor_mapDerivedCategory_obj
        (S.isZero_homologyFunctor_mapDerivedCategory_obj
          (R.isZero_homologyFunctor_mapDerivedCategory_obj hq))
  have hPb : DerivedCategory.TStructure.t.bounded P := by
    obtain ⟨a, b, hb⟩ := hbounded
    exact ⟨⟨a, (DerivedCategory.isGE_iff P a).mpr (fun q hq ↦ hz q (hb q (.inl hq)))⟩,
      ⟨b, (DerivedCategory.isLE_iff P b).mpr (fun q hq ↦ hz q (hb q (.inr hq)))⟩⟩
  have hPc (q : ℤ) : ProEtale.IsConstructible B
      ((DerivedCategory.homologyFunctor _ q).obj P) := by
    refine ⟨identityStratification Y, fun i ↦ ?_⟩
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((ProEtale.upperStarId (ModuleCat.{u + 1} B) Y).app _).symm (hP q)
  obtain ⟨L, _, ⟨eL⟩⟩ := origin_boundedConstructible_of_homology B hPb
    (fun q ↦ ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj B (hPc q))
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y
  have hLH (q : ℤ) : F.obj ((DerivedCategory.homologyFunctor _ q).obj L) ≅
      (DerivedCategory.homologyFunctor _ q).obj P :=
    (F.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso eL
  have hLl (q : ℤ) : IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj L) :=
    ProEtale.isFiniteLocallyConstantSheaf_of_comparison_finite_models B _ (by
      obtain ⟨ι, W, g, hW, hM⟩ := ProEtale.isFiniteLocallyConstant_of_iso (hLH q).symm (hP q)
      exact ⟨ι, W, g, hW, fun i ↦
        let ⟨M, _, e⟩ := hM i; ⟨M, Module.finite_of_finite B, e⟩⟩)
  have hLz (q : ℤ) (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L) :=
    F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((hz q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso eL))
  let T := Sheaf.restrictScalars Y.smallEtaleTopology eBC.symm.toRingHom
  let U := AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} C) V.hom
  let level := U.mapDerivedCategory.obj (T.mapDerivedCategory.obj L)
  refine ⟨{ level := level
            lisse := ?_
            vanishing := ?_
            refinementLisse := ?_
            comparison := ?_ }⟩
  · intro q
    have hs : IsFiniteLocallyConstantSheaf
        (T.obj ((DerivedCategory.homologyFunctor _ q).obj L)) :=
      FiniteQuotientOriginProof.scalar_lisse eBC.symm.toRingHom _ (hLl q)
    have hT : IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor _ q).obj (T.mapDerivedCategory.obj L)) :=
      IsFiniteLocallyConstantSheaf.of_iso
        (F := T.obj ((DerivedCategory.homologyFunctor _ q).obj L))
        ((T.mapDerivedCategoryHomologyFunctorIso q).app L)
    have := hT
    have hu : IsFiniteLocallyConstantSheaf
        (U.obj ((DerivedCategory.homologyFunctor _ q).obj (T.mapDerivedCategory.obj L))) :=
      IsFiniteLocallyConstantSheaf.upperStar (X := Y) (Y := V.left) V.hom
        ((DerivedCategory.homologyFunctor _ q).obj (T.mapDerivedCategory.obj L))
    exact IsFiniteLocallyConstantSheaf.of_iso
      (F := U.obj ((DerivedCategory.homologyFunctor _ q).obj (T.mapDerivedCategory.obj L)))
      ((U.mapDerivedCategoryHomologyFunctorIso q).app (T.mapDerivedCategory.obj L))
  · intro q hq
    exact U.isZero_homologyFunctor_mapDerivedCategory_obj
      (T.isZero_homologyFunctor_mapDerivedCategory_obj (hLz q hq))
  · intro W _w q
    apply (relativeFinite_iff (W.hom ≫ g) B _).mpr
    apply (fixedFiniteModels_iff W.left B _).mpr
    apply ProEtale.isFiniteLocallyConstant_of_iso
      (FiniteQuotientOriginProof.fixedHomologyIso (W.hom ≫ g) d n K q).symm
    let H := ProEtale.upperStar (ModuleCat.{u + 1} B) W.hom
    let c := (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarComp (ModuleCat.{u + 1} B) W.hom g)).app J ≪≫
        ((Functor.mapDerivedCategoryCompIso
          (ProEtale.upperStar (ModuleCat.{u + 1} B) g) H).app J).symm
    have := hLl q
    let E : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} B) :=
      AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) W.hom
    have : IsFiniteLocallyConstantSheaf
        (E.obj ((DerivedCategory.homologyFunctor _ q).obj L)) :=
      IsFiniteLocallyConstantSheaf.upperStar (X := Y) (Y := W.left) W.hom
        ((DerivedCategory.homologyFunctor _ q).obj L)
    have hW : ProEtale.IsFiniteLocallyConstant B
        (H.obj ((DerivedCategory.homologyFunctor _ q).obj P)) :=
      ProEtale.isFiniteLocallyConstant_of_iso
        (((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B)
          (X := Y) (Y := W.left) W.hom).app
            ((DerivedCategory.homologyFunctor _ q).obj L)).symm ≪≫
            H.mapIso (hLH q))
        (ProEtale.isFiniteLocallyConstant_comparisonUpperStar_obj
          (X := W.left) (E.obj ((DerivedCategory.homologyFunctor _ q).obj L)))
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((H.mapDerivedCategoryHomologyFunctorIso q).app P ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso c.symm) hW
  · let Q := Sheaf.restrictScalars Y.smallEtaleTopology eBC.toRingHom
    let QV := Sheaf.restrictScalars V.left.smallEtaleTopology eBC.toRingHom
    let UB := AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) V.hom
    let FV := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) V.left
    let HV := ProEtale.upperStar (ModuleCat.{u + 1} B) V.hom
    let eQ : T ⋙ Q ≅ 𝟭 _ :=
      NatIso.ofComponents (fun M ↦
        (fullyFaithfulSheafToPresheaf Y.smallEtaleTopology _).preimageIso
          (Functor.isoWhiskerLeft M.obj
            (ModuleCat.restrictScalarsEquivalenceOfRingEquiv eBC).counitIso))
        (by intro M N f; ext U x; rfl)
    let eU := Functor.mapDerivedCategoryCompIso Q UB ≪≫
      Functor.mapDerivedCategoryNatIso
        (AlgebraicGeometry.Etale.upperStarRestrictScalarsIsoSheaf eBC.toRingHom V.hom) ≪≫
          (Functor.mapDerivedCategoryCompIso U QV).symm
    let eT := Functor.mapDerivedCategoryCompIso T Q ≪≫
      Functor.mapDerivedCategoryNatIso eQ ≪≫ Functor.mapDerivedCategoryIdIso _
    let eF := Functor.mapDerivedCategoryCompIso UB FV ≪≫
      Functor.mapDerivedCategoryNatIso
        (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) V.hom).symm ≪≫
          (Functor.mapDerivedCategoryCompIso F HV).symm
    let eV := (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarComp (ModuleCat.{u + 1} B) V.hom g)).app J ≪≫
        ((Functor.mapDerivedCategoryCompIso
          (ProEtale.upperStar (ModuleCat.{u + 1} B) g) HV).app J).symm
    exact ⟨FV.mapDerivedCategory.mapIso ((eU.app (T.mapDerivedCategory.obj L)).symm ≪≫
        UB.mapDerivedCategory.mapIso (eT.app L)) ≪≫
      eF.app L ≪≫ HV.mapDerivedCategory.mapIso eL ≪≫ eV.symm⟩

end AlgebraicGeometry.Scheme
