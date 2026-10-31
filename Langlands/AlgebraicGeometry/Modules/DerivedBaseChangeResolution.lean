import Langlands.Cohomology.AcyclicResolution.DerivedComposition
import Langlands.AlgebraicGeometry.Modules.BaseChangeResolution

/-! # Actual derived base change through compatible right resolutions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

section Pushforward

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}
  (g : Y ⟶ X) (f : X ⟶ Spec R)
  {M : X.Modules} {N : Y.Modules}
  {K : CochainComplex X.Modules ℕ} {L : CochainComplex Y.Modules ℕ}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]
  (η : (CochainComplex.single₀ Y.Modules).obj N ⟶ L) [QuasiIso η]
  [QuasiIso (mapResolutionAugmentation (Scheme.Modules.pushforward g) η)]
  (a : M ⟶ (Scheme.Modules.pushforward g).obj N)
  (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
  (ht : ε ≫ t = (CochainComplex.single₀ X.Modules).map a ≫
    mapResolutionAugmentation (Scheme.Modules.pushforward g) η)

include ht in
/-- The inverse of the actual derived pushforward comparison is computed
through any compatible right resolutions. -/
@[reassoc]
theorem derivedResolutionComparison_inv_pushforwardComparison
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj N)) :
    derivedResolutionComparison (relativeGlobalSections f) ε ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙
          DerivedCategory.Plus.ι).map a ≫
        (derivedPushforwardComparisonIso g f N hN).inv =
      (derivedResolutionFunctor (relativeGlobalSections f)).map t ≫
        (derivedCompResolutionIso (relativeGlobalSections f)
          (relativeGlobalSectionsCompIso g f) L).inv ≫
        derivedResolutionComparison (relativeGlobalSections (g ≫ f)) η := by
  have hn := derivedResolutionComparison_naturality (relativeGlobalSections f) ε
    (mapResolutionAugmentation (Scheme.Modules.pushforward g) η) a t ht
  have hs :
      (derivedCompResolutionIso (relativeGlobalSections f)
        (relativeGlobalSectionsCompIso g f) L).inv ≫
          derivedResolutionComparison (relativeGlobalSections (g ≫ f)) η ≫
          (derivedPushforwardComparisonIso g f N hN).hom =
        derivedResolutionComparison (relativeGlobalSections f)
          (mapResolutionAugmentation (Scheme.Modules.pushforward g) η) := by
    rw [derivedPushforwardComparisonIso_hom]
    change _ ≫ derivedResolutionComparison (relativeGlobalSections (g ≫ f)) η ≫
      derivedCompComparison (relativeGlobalSections f)
        (relativeGlobalSectionsCompIso g f) N hN = _
    rw [derivedResolutionComparison_compComparison, Iso.inv_hom_id_assoc]
  apply (cancel_mono (derivedPushforwardComparisonIso g f N hN).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hs]
  exact hn.symm

end Pushforward

section BaseChange

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  {K : CochainComplex X.Modules ℕ} {L : CochainComplex Y.Modules ℕ}

/-- The specified semilinear derived map on two natural-indexed complexes:
apply sections to the cochain map into the pushforward, undo the
pushforward-composition comparison, and restrict scalars on the target. -/
def derivedResolutionBaseChangeMap
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) :
    (derivedResolutionFunctor (relativeGlobalSections f)).obj K ⟶
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        ((derivedResolutionFunctor (relativeGlobalSections f')).obj L) :=
  (derivedResolutionFunctor (relativeGlobalSections f)).map t ≫
    (derivedCompResolutionIso (relativeGlobalSections f)
      (relativeGlobalSectionsCompIso g f) L).inv ≫
    (derivedResolutionPostcompIso (relativeGlobalSections f')
      (ModuleCat.restrictScalars φ.hom)
      (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) L).inv

variable {M : X.Modules}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]
  (η : (CochainComplex.single₀ Y.Modules).obj ((Scheme.Modules.pullback g).obj M) ⟶ L)
  [QuasiIso η]
  [QuasiIso (mapResolutionAugmentation (Scheme.Modules.pushforward g) η)]
  (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
  (ht : ε ≫ t =
    (CochainComplex.single₀ X.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward g) η)

include ht in
/-- The specified map on compatible resolutions computes the actual
derived base-change morphism. No flatness of the base-ring map is required. -/
@[reassoc]
theorem derivedResolutionComparison_baseChangeMap
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M))) :
    derivedResolutionComparison (relativeGlobalSections f) ε ≫
        derivedBaseChangeMap φ f f' g w M hM =
      derivedResolutionBaseChangeMap φ f f' g w t ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (derivedResolutionComparison (relativeGlobalSections f') η) := by
  have hp := derivedResolutionComparison_inv_pushforwardComparison g f ε η
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) t ht hM
  have h := congrArg (fun k => k ≫
    (DerivedPlus.derivedCompIso (relativeGlobalSections f')
      (ModuleCat.restrictScalars φ.hom)
      (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).inv.app
        ((Scheme.Modules.pullback g).obj M)) hp
  simpa only [derivedBaseChangeMap, derivedResolutionBaseChangeMap, Category.assoc,
    derivedResolutionComparison_inv_derivedCompIso] using h

end BaseChange

end Langlands.AlgebraicGeometry.Modules.DerivedSections
