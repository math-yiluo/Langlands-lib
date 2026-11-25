/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteHeartRealization
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Monoidal comparison of the finite-coefficient hearts

## References

* Stacks Tags 03ET, 00YV and 03CY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

section HeartProof

-- Fix the coefficient universe rather than inferring a parameter beneath `max`.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify

private def continuousConstants (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj
        (RingCat.of (ULift.{u + 1, u} (ULift.{u, 0} A))) ⟶
      (continuousMapRingSheaf X A).obj where
  app U := RingCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const U.unop.left a.down.down)
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl }
  naturality _ _ _ := rfl

private instance continuousConstants_injective (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (continuousConstants X A) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst b
      exact (Scheme.ProEt.topology X).superset_covering (fun _ _ _ ↦ rfl)
        ((Scheme.ProEt.topology X).top_mem _)
    · have : IsEmpty U.unop.left := ⟨fun x ↦ hab (by
        have hh := congrArg (fun f : ULift.{u + 1} C(U.unop.left, A) ↦ f.down x) h
        exact ULift.ext (ULift.ext hh))⟩
      exact Scheme.ProEt.mem_topology_of_openImmersion _
        (fun _ : PEmpty.{u + 1} ↦ 𝟙 U.unop.left) (fun x ↦ isEmptyElim x) fun i ↦ i.elim

private instance continuousConstants_surjective (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (continuousConstants X A) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, A) := s₀.down
    let j (a : ULift.{u} A) := (U.left.fiberOpens s a.down).ι
    refine Scheme.ProEt.mem_topology_of_openImmersion _ j
      (fun x ↦ ⟨⟨s x⟩, ⟨x, rfl⟩, ?_⟩) fun a ↦ ?_
    · exact Scheme.Opens.ι_apply _ _
    · refine ⟨ULift.up a, ULift.ext (ContinuousMap.ext fun x ↦ ?_)⟩
      exact x.2.symm

private theorem fixedScalars_equivalence (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] :
    (integralModelFixedScalars X A).IsEquivalence := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let J := Scheme.ProEt.topology X
  let B := ULift.{u + 1, u} (ULift.{u, 0} A)
  let α := continuousConstants X A
  let E := sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
    finiteCoefficientModulePresheaf X.ProEt B
  let S := PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} α
  let L := E ⋙ S
  have : L.IsEquivalence := intrinsicRealization_isEquivalence.{u} J B _ α
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1} α
  let η : 𝟭 (Sheaf J (ModuleCat.{u + 1} B)) ⟶ L ⋙ integralModelFixedScalars X A :=
    { app N := ObjectProperty.homMk
        { app U := (adj.unit.app (E.obj N)).app U
          naturality U V f := by
            ext x
            exact PresheafOfModules.naturality_apply (adj.unit.app (E.obj N)) f x }
      naturality N M f := by
        ext U x
        exact ConcreteCategory.congr_hom (congrArg
          (fun g ↦ g.app U) (adj.unit.naturality (E.map f))) x }
  have hη : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    have hunit : IsIso (adj.unit.app (E.obj N)) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf.{u + 1} _)]
      change IsIso (toSheafify J _)
      exact isIso_toSheafify J
        ((sheafCompose J (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).obj N).property
    have : IsIso ((sheafToPresheaf J (ModuleCat.{u + 1} B)).map (η.app N)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      exact Functor.map_isIso (PresheafOfModules.evaluation _ U)
        (adj.unit.app (E.obj N))
    exact isIso_of_reflects_iso _ (sheafToPresheaf J (ModuleCat.{u + 1} B))
  have : (L ⋙ integralModelFixedScalars X A).IsEquivalence :=
    Functor.isEquivalence_of_iso (asIso η)
  exact Functor.isEquivalence_of_comp_left L (integralModelFixedScalars X A)

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- Compare the specified heart realization with the coefficient-sized module category.
There is no derived-category or constructibility assertion here. -/
theorem finiteHeartMonoidalPresentation
    (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    let R := ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1, 0} A)
    letI := SheafOfModules.monoidalCategory R
    (integralModelIntrinsicRealization X A).IsEquivalence ∧
      ∃ H : Scheme.proEtaleRingModules X
          (Scheme.proEtaleConstantRing X (ULift.{u, 0} A)) ≌ ConstantCompletion.Mod R,
        ∃ (_ : H.functor.Additive),
          Nonempty (finiteHeartRealization X A ⋙ H.functor).Monoidal := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let R := ConstantCompletion.constant
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1, 0} A)
  let : MonoidalCategory (ConstantCompletion.Mod R) := SheafOfModules.monoidalCategory R
  let I := integralModelIntrinsicRealization X A
  have hI : I.IsEquivalence := by
    have := fixedScalars_equivalence X A
    have := (finiteCoefficientIntrinsicRealization_exact.{u} X (ULift.{u, 0} A)).1
    unfold I integralModelIntrinsicRealization
    infer_instance
  let := hI
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let := heR
  let P := finiteComparisonRealization A X eR
  have : P.IsEquivalence := (finiteComparisonRealization_exact A X eR).1
  obtain ⟨mP⟩ := finiteRealizationMonoidal_exists.{u} A X eR
  let : P.Monoidal := mP
  let Q := finiteComparisonProEtaleModelRealization X (ULift.{u + 1} A)
  let : Q.Monoidal := proRealization_monoidal.{u} X (ULift.{u + 1} A)
  let K := P.asEquivalence.symm.trans Q.asEquivalence.symm
  let : K.functor.Monoidal := by
    letI : P.asEquivalence.functor.Monoidal := by
      change P.Monoidal
      exact mP
    letI : Q.asEquivalence.functor.Monoidal := by
      change Q.Monoidal
      exact proRealization_monoidal.{u} X (ULift.{u + 1} A)
    letI := P.asEquivalence.inverseMonoidal
    letI := Q.asEquivalence.inverseMonoidal
    exact inferInstanceAs (P.asEquivalence.inverse ⋙ Q.asEquivalence.inverse).Monoidal
  let H := I.asEquivalence.symm.trans K
  have hH : H.functor.Additive := Functor.additive_of_preserves_binary_products _
  refine ⟨hI, H, hH, ?_⟩
  have := finiteScalarMap_isIso X A
  let S := Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (finiteScalarMap X A)
  let : S.Monoidal := inferInstance
  let c : finiteHeartRealization X A ⋙ H.functor ≅ S ⋙ K.functor :=
    Functor.associator S I H.functor ≪≫
      Functor.isoWhiskerLeft S
        ((Functor.associator I I.asEquivalence.inverse K.functor).symm ≪≫
          Functor.isoWhiskerRight I.asEquivalence.unitIso.symm K.functor ≪≫
          Functor.leftUnitor K.functor)
  exact ⟨Functor.Monoidal.transport c.symm⟩

end HeartProof

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
