import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCompositionProof
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof

/-! # Pushforward comparison for canonical cohomology pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}} {X Y Z : Over (Spec R)}

/-- The cohomological form of the derived pushforward comparison used by
the canonical pullback, without a higher-direct-image vanishing assumption. -/
def canonicalPushforwardCohomologyMap (f : Y ⟶ X) (N : Y.left.Modules) (n : ℕ) :
    (relativeCohomology X.hom n).obj ((Scheme.Modules.pushforward f.left).obj N) ⟶
      (relativeCohomology Y.hom n).obj N :=
  (DerivedPlus.homologyIso (relativeGlobalSections X.hom)
      (injectiveResolution ((Scheme.Modules.pushforward f.left).obj N)) n).inv ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
      ((pushforwardSingleDerivedSectionsComparison f).app N) ≫
    (DerivedPlus.homologyIso (relativeGlobalSections Y.hom)
      (injectiveResolution N) n).hom

@[reassoc]
lemma canonicalPushforwardCohomologyMap_naturality (f : Y ⟶ X)
    {M N : Y.left.Modules} (a : M ⟶ N) (n : ℕ) :
    (relativeCohomology X.hom n).map ((Scheme.Modules.pushforward f.left).map a) ≫
        canonicalPushforwardCohomologyMap f N n =
      canonicalPushforwardCohomologyMap f M n ≫ (relativeCohomology Y.hom n).map a := by
  have hX := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections X.hom)
    ((Scheme.Modules.pushforward f.left).map a)
    (injectiveResolution ((Scheme.Modules.pushforward f.left).obj M))
    (injectiveResolution ((Scheme.Modules.pushforward f.left).obj N)) n
  have hY := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections Y.hom)
    a (injectiveResolution M) (injectiveResolution N) n
  have hD := congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
    ((pushforwardSingleDerivedSectionsComparison f).naturality a)
  simp only [Functor.comp_map, Functor.map_comp] at hD
  have hX' : (relativeCohomology X.hom n).map ((Scheme.Modules.pushforward f.left).map a) ≫
      (DerivedPlus.homologyIso (relativeGlobalSections X.hom)
        (injectiveResolution ((Scheme.Modules.pushforward f.left).obj N)) n).inv =
    (DerivedPlus.homologyIso (relativeGlobalSections X.hom)
      (injectiveResolution ((Scheme.Modules.pushforward f.left).obj M)) n).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        ((DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map
          ((Scheme.Modules.pushforward f.left).map a)) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hX.symm
  simp only [canonicalPushforwardCohomologyMap, Category.assoc]
  rw [reassoc_of% hX', reassoc_of% hD, hY]
  rfl

/-- Canonical cohomology pullback factors through the actual adjunction unit. -/
lemma relativeCohomologyPullback_eq_unit_pushforward (f : Y ⟶ X)
    (M : X.left.Modules) (n : ℕ) :
    relativeCohomologyPullback f M n =
      (relativeCohomology X.hom n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app M) ≫
        canonicalPushforwardCohomologyMap f ((Scheme.Modules.pullback f.left).obj M) n := by
  have h := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections X.hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app M)
    (injectiveResolution M)
    (injectiveResolution ((Scheme.Modules.pushforward f.left).obj
      ((Scheme.Modules.pullback f.left).obj M))) n
  have h' : (relativeCohomology X.hom n).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app M) ≫
      (DerivedPlus.homologyIso (relativeGlobalSections X.hom)
        (injectiveResolution ((Scheme.Modules.pushforward f.left).obj
          ((Scheme.Modules.pullback f.left).obj M))) n).inv =
    (DerivedPlus.homologyIso (relativeGlobalSections X.hom)
      (injectiveResolution M) n).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        ((DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app M)) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact h.symm
  simp only [relativeCohomologyPullback, relativeDerivedSectionsPullback_eq_unit_comparison,
    Functor.map_comp, canonicalPushforwardCohomologyMap, Category.assoc]
  dsimp only [relativeCohomology] at h' ⊢
  rw [reassoc_of% h']

/-- A coefficient pullback is cohomology of its adjoint followed by the
canonical pushforward comparison. -/
lemma relativeCohomologyPullback_coefficient (f : Y ⟶ X)
    {M : X.left.Modules} {N : Y.left.Modules}
    (a : (Scheme.Modules.pullback f.left).obj M ⟶ N) (n : ℕ) :
    relativeCohomologyPullback f M n ≫ (relativeCohomology Y.hom n).map a =
      (relativeCohomology X.hom n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _ a) ≫
        canonicalPushforwardCohomologyMap f N n := by
  rw [relativeCohomologyPullback_eq_unit_pushforward, Category.assoc,
    ← canonicalPushforwardCohomologyMap_naturality, ← Functor.map_comp_assoc]
  rfl

/-- Composition of the canonical comparison uses the actual pushforward
composition isomorphism. -/
@[reassoc]
lemma canonicalPushforwardCohomologyMap_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    (N : Z.left.Modules) (n : ℕ) :
    canonicalPushforwardCohomologyMap f ((Scheme.Modules.pushforward g.left).obj N) n ≫
        canonicalPushforwardCohomologyMap g N n =
      (relativeCohomology X.hom n).map
          ((Scheme.Modules.pushforwardComp g.left f.left).hom.app N) ≫
        canonicalPushforwardCohomologyMap (g ≫ f) N n := by
  have hX := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections X.hom)
    ((Scheme.Modules.pushforwardComp g.left f.left).hom.app N)
    (injectiveResolution ((Scheme.Modules.pushforward f.left).obj
      ((Scheme.Modules.pushforward g.left).obj N)))
    (injectiveResolution ((Scheme.Modules.pushforward (g ≫ f).left).obj N)) n
  have hD := congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
    (pushforwardSingleDerivedSectionsComparison_comp f g N)
  simp only [Functor.map_comp] at hD
  have hX' : (relativeCohomology X.hom n).map
        ((Scheme.Modules.pushforwardComp g.left f.left).hom.app N) ≫
      (DerivedPlus.homologyIso (relativeGlobalSections X.hom)
        (injectiveResolution ((Scheme.Modules.pushforward (g ≫ f).left).obj N)) n).inv =
    (DerivedPlus.homologyIso (relativeGlobalSections X.hom)
      (injectiveResolution ((Scheme.Modules.pushforward f.left).obj
        ((Scheme.Modules.pushforward g.left).obj N))) n).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
        ((DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map
          ((Scheme.Modules.pushforwardComp g.left f.left).hom.app N)) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hX.symm
  simp only [canonicalPushforwardCohomologyMap, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [relativeCohomology] at hX' ⊢
  rw [reassoc_of% hD, reassoc_of% hX']

/-- The derived comparison is an isomorphism on every injective resolution. -/
lemma isIso_pushforwardDerivedSectionsComparison_resolution (f : Y ⟶ X)
    (N : Y.left.Modules) :
    IsIso ((pushforwardDerivedSectionsComparison f).app
      (DerivedPlus.resolutionPlus (injectiveResolution N))) := by
  let K := DerivedPlus.resolutionPlus (injectiveResolution N)
  have hU : IsIso ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
      ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K)) := by
    apply acyclicTermsDerivedUnitStatement
    intro i q
    exact (pushforwardInjectiveAcyclic Y.left X.left f.left (K.obj.X i)
      inferInstance q).2 R X.hom
  have hF := pushforwardDerivedSectionsComparison_fac f K
  have : IsIso ((relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K) ≫
      (pushforwardDerivedSectionsComparison f).app K) := by
    rw [hF]
    dsimp only [K]
    infer_instance
  exact (isIso_comp_left_iff _ _).1 this

/-- A closed immersion makes the canonical derived comparison invertible. -/
lemma isIso_pushforwardSingleDerivedSectionsComparison_closedImmersion (f : Y ⟶ X)
    [IsClosedImmersion f.left] (N : Y.left.Modules) :
    IsIso ((pushforwardSingleDerivedSectionsComparison f).app N) := by
  have := ClosedImmersionHigherDirectImageVanishing.pushforward_preservesEpimorphisms f.left
  have : (Scheme.Modules.pushforward f.left).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let I := injectiveResolution N
  let a := DerivedPlus.resolutionPlusι I
  have : IsIso (DerivedCategory.Plus.Q.map a) := by
    dsimp only [a]
    infer_instance
  have : IsIso ((DerivedCategory.Plus.Q ⋙
      (relativeGlobalSections Y.hom).rightDerivedFunctorPlus).map a) := by
    change IsIso ((relativeGlobalSections Y.hom).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map a))
    infer_instance
  have hβ := (pushforwardDerivedSectionsComparison f).naturality a
  have hQa : IsIso (DerivedCategory.Plus.Q.map
      ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.map a)) := by
    apply Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.left.Modules)
    change QuasiIso ((Scheme.Modules.pushforward f.left).mapHomologicalComplex _ |>.map I.ι')
    infer_instance
  have : IsIso ((pushforwardDerivedSectionsComparison f).app
      (DerivedPlus.resolutionPlus I)) :=
    isIso_pushforwardDerivedSectionsComparison_resolution f N
  have hB : IsIso ((pushforwardDerivedSectionsComparison f).app
      ((DerivedPlus.singlePlusFunctor Y.left.Modules).obj N)) := by
    have hC : IsIso ((pushforwardDerivedSectionsComparison f).app
          ((DerivedPlus.singlePlusFunctor Y.left.Modules).obj N) ≫
        (DerivedCategory.Plus.Q ⋙
          (relativeGlobalSections Y.hom).rightDerivedFunctorPlus).map a) := by
      rw [← hβ]
      change IsIso ((relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.map a)) ≫ _)
      infer_instance
    exact (isIso_comp_right_iff _ _).1 hC
  dsimp only [pushforwardSingleDerivedSectionsComparison, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app]
  infer_instance

/-- Canonical coefficient cohomology of a closed-immersion pushforward is
isomorphic to cohomology on the closed subscheme. -/
lemma isIso_canonicalPushforwardCohomologyMap_closedImmersion (f : Y ⟶ X)
    [IsClosedImmersion f.left] (N : Y.left.Modules) (n : ℕ) :
    IsIso (canonicalPushforwardCohomologyMap f N n) := by
  have := isIso_pushforwardSingleDerivedSectionsComparison_closedImmersion f N
  unfold canonicalPushforwardCohomologyMap
  infer_instance

end Langlands.AlgebraicGeometry.Modules.DerivedSections
