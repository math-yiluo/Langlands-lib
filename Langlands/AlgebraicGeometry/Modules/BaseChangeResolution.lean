import Langlands.Cohomology.AcyclicResolution.ExactComparison
import Langlands.AlgebraicGeometry.Modules.DerivedBaseChange
import Langlands.AlgebraicGeometry.Modules.ScalarCohomologyBaseChange

/-! # Canonical base change through compatible right resolutions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section Pushforward

variable {X X' : Scheme.{u}} {R : CommRingCat.{u}}
  (g : X' ⟶ X) (f : X ⟶ Spec R)
  {M : X.Modules} {N : X'.Modules}
  {K : CochainComplex X.Modules ℕ} {L : CochainComplex X'.Modules ℕ}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]
  (η : (CochainComplex.single₀ X'.Modules).obj N ⟶ L) [QuasiIso η]
  [QuasiIso (mapResolutionAugmentation (Scheme.Modules.pushforward g) η)]
  (a : M ⟶ (Scheme.Modules.pushforward g).obj N)
  (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
  (ht : ε ≫ t = (CochainComplex.single₀ X.Modules).map a ≫
    mapResolutionAugmentation (Scheme.Modules.pushforward g) η)

include ht in
/-- Compute the inverse pushforward comparison through compatible arbitrary resolutions. -/
@[reassoc]
theorem resolutionComparison_inv_pushforwardComparison
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj N))
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)))
    (n : ℕ) :
    resolutionComparison (relativeGlobalSections f) ε n ≫
        (relativeCohomology f n).map a ≫
        @inv _ _ _ _ (pushforwardComparison g f N hN n)
          (isIso_pushforwardComparison g f N hN hJ n) =
      (homologyFunctor (ModuleCat R) _ n).map
          (((relativeGlobalSections f).mapHomologicalComplex _).map t ≫
            (Functor.mapHomologicalComplexCompIso (relativeGlobalSectionsCompIso g f) _).hom.app L) ≫
        resolutionComparison (relativeGlobalSections (g ≫ f)) η n := by
  have := isIso_pushforwardComparison g f N hN hJ n
  have hc := resolutionComparison_compComparison (relativeGlobalSections f)
    (relativeGlobalSectionsCompIso g f) η hN n
  have hn := resolutionComparison_naturality (relativeGlobalSections f) ε
    (mapResolutionAugmentation (Scheme.Modules.pushforward g) η) a t ht n
  let c : ((relativeGlobalSections (g ≫ f)).rightDerived n).obj N ⟶
      ((relativeGlobalSections f).rightDerived n).obj ((Scheme.Modules.pushforward g).obj N) :=
    pushforwardComparison g f N hN n
  have : IsIso c := isIso_pushforwardComparison g f N hN hJ n
  have hs : (homologyFunctor (ModuleCat R) _ n).map
        ((Functor.mapHomologicalComplexCompIso (relativeGlobalSectionsCompIso g f) _).hom.app L) ≫
      resolutionComparison (relativeGlobalSections (g ≫ f)) η n ≫
      pushforwardComparison g f N hN n =
        resolutionComparison (relativeGlobalSections f)
          (mapResolutionAugmentation (Scheme.Modules.pushforward g) η) n := by
    change _ ≫ resolutionComparison (relativeGlobalSections (g ≫ f)) η n ≫
      compComparison (relativeGlobalSections f) (relativeGlobalSectionsCompIso g f) N hN n = _
    erw [
      hc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  change _ ≫ resolutionComparison (relativeGlobalSections (g ≫ f)) η n ≫ c = _ at hs
  change resolutionComparison (relativeGlobalSections f) ε n ≫
    ((relativeGlobalSections f).rightDerived n).map a ≫ inv c = _
  apply (cancel_mono c).1
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hs]
  exact hn.symm

end Pushforward

section BaseRing

variable {X : Scheme.{u}} {R R' : CommRingCat.{u}}
  (φ : R ⟶ R') (f : X ⟶ Spec R) (f' : X ⟶ Spec R')
  (w : f = f' ≫ Spec.map φ)
  {M : X.Modules} {K : CochainComplex X.Modules ℕ}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]

/-- The published base-ring comparison is computed on any right resolution. -/
@[reassoc]
theorem resolutionComparison_baseRingIso (n : ℕ) :
    resolutionComparison (relativeGlobalSections f) ε n ≫
        (relativeCohomologyBaseRingIso φ f f' w n).hom.app M =
      (homologyFunctor (ModuleCat R) _ n).map
          ((Functor.mapHomologicalComplexCompIso
            (relativeGlobalSectionsBaseRingIso φ f f' w) _).inv.app K) ≫
        (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
          (((relativeGlobalSections f').mapHomologicalComplex _).obj K) n).hom ≫
        (ModuleCat.restrictScalars φ.hom).map
          (resolutionComparison (relativeGlobalSections f') ε n) := by
  have h := resolutionComparison_inv_rightDerivedCompIsoOfResolution
    (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom)
    (relativeGlobalSectionsBaseRingIso φ f f' w) ε n
  rw [rightDerivedCompIsoOfResolution_baseRingIso, Iso.symm_inv, Iso.app_hom] at h
  exact h

end BaseRing

section BaseChange

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}}
  (φ : R ⟶ R') (f : X ⟶ Spec R) (f' : X' ⟶ Spec R')
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  {K : CochainComplex X.Modules ℕ} {L : CochainComplex X'.Modules ℕ}

/-- The semilinear cochain map on sections induced by a cochain map into
the pushforward complex and the specified commuting square. -/
def resolutionSectionsBaseChangeMap
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) :
    ((relativeGlobalSections f).mapHomologicalComplex _).obj K ⟶
      ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).obj
        (((relativeGlobalSections f').mapHomologicalComplex _).obj L) :=
  ((relativeGlobalSections f).mapHomologicalComplex _).map t ≫
    (Functor.mapHomologicalComplexCompIso (relativeGlobalSectionsCompIso g f) _).hom.app L ≫
    (Functor.mapHomologicalComplexCompIso
      (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) _).inv.app L

/-- Each component uses the actual sections map and the two specified sections
comparisons. -/
@[simp]
lemma resolutionSectionsBaseChangeMap_f
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) (q : ℕ) :
    (resolutionSectionsBaseChangeMap φ f f' g w t).f q =
      (relativeGlobalSections f).map (t.f q) ≫
        (relativeGlobalSectionsCompIso g f).hom.app (L.X q) ≫
        (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).inv.app (L.X q) :=
  rfl

/-- The cochain sections construction respects a compatible square of cochain
maps on the source and target. -/
@[reassoc]
lemma resolutionSectionsBaseChangeMap_naturality
    {K' : CochainComplex X.Modules ℕ} {L' : CochainComplex X'.Modules ℕ}
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
    (t' : K' ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L')
    (a : K ⟶ K') (b : L ⟶ L')
    (ht : a ≫ t' = t ≫ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).map b) :
    ((relativeGlobalSections f).mapHomologicalComplex _).map a ≫
        resolutionSectionsBaseChangeMap φ f f' g w t' =
      resolutionSectionsBaseChangeMap φ f f' g w t ≫
        ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
          (((relativeGlobalSections f').mapHomologicalComplex _).map b) := by
  have hc := (Functor.mapHomologicalComplexCompIso
    (relativeGlobalSectionsCompIso g f) (ComplexShape.up ℕ)).hom.naturality b
  have hb := (Functor.mapHomologicalComplexCompIso
    (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w) (ComplexShape.up ℕ)).inv.naturality b
  simp only [Functor.comp_map] at hc hb
  simp only [resolutionSectionsBaseChangeMap, Category.assoc]
  rw [← Functor.map_comp_assoc, ht, Functor.map_comp_assoc, reassoc_of% hc, hb]

/-- The scalar-linear adjunct on cohomology of the semilinear cochain
sections map. This does not require flatness of the scalar extension. -/
def scalarResolutionCohomologyMap
    (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L) (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj
        ((homologyFunctor (ModuleCat R) _ n).obj
          (((relativeGlobalSections f).mapHomologicalComplex _).obj K)) ⟶
      (homologyFunctor (ModuleCat R') _ n).obj
        (((relativeGlobalSections f').mapHomologicalComplex _).obj L) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    ((homologyFunctor (ModuleCat R) _ n).map
        (resolutionSectionsBaseChangeMap φ f f' g w t) ≫
      (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
        (((relativeGlobalSections f').mapHomologicalComplex _).obj L) n).hom)

variable {M : X.Modules}
  (ε : (CochainComplex.single₀ X.Modules).obj M ⟶ K) [QuasiIso ε]
  (η : (CochainComplex.single₀ X'.Modules).obj ((Scheme.Modules.pullback g).obj M) ⟶ L)
  [QuasiIso η]
  [QuasiIso (mapResolutionAugmentation (Scheme.Modules.pushforward g) η)]
  (t : K ⟶ ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj L)
  (ht : ε ≫ t =
    (CochainComplex.single₀ X.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward g) η)

include ht in
/-- The actual canonical base-change map is computed by the specified compatible
resolutions and their cochain sections map. -/
@[reassoc]
theorem resolutionComparison_baseChangeMap
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M)))
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)))
    (n : ℕ) :
    resolutionComparison (relativeGlobalSections f) ε n ≫
        baseChangeMap φ f f' g w M hM hJ n =
      (homologyFunctor (ModuleCat R) _ n).map
          (resolutionSectionsBaseChangeMap φ f f' g w t) ≫
        (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
          (((relativeGlobalSections f').mapHomologicalComplex _).obj L) n).hom ≫
        (ModuleCat.restrictScalars φ.hom).map
          (resolutionComparison (relativeGlobalSections f') η n) := by
  have hp := resolutionComparison_inv_pushforwardComparison g f ε η
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) t ht hM hJ n
  have h := congrArg (fun z => z ≫
    (relativeCohomologyBaseRingIso φ (g ≫ f) f' w n).hom.app
      ((Scheme.Modules.pullback g).obj M)) hp
  have hb := resolutionComparison_baseRingIso φ (g ≫ f) f' w η n
  dsimp only [relativeCohomology] at h hb
  simp only [Category.assoc] at h
  rw [hb] at h
  simpa only [baseChangeMap, resolutionSectionsBaseChangeMap, Functor.map_comp,
    relativeCohomology, Functor.comp_obj, Category.assoc] using h

include ht in
/-- The exact scalar-linear canonical base-change map is computed through the
same compatible right resolutions. -/
@[reassoc]
theorem resolutionComparison_scalarBaseChangeMap
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj
      ((Scheme.Modules.pullback g).obj M)))
    (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).map
        (resolutionComparison (relativeGlobalSections f) ε n) ≫
        scalarBaseChangeMap φ f f' g w M hM n =
      scalarResolutionCohomologyMap φ f f' g w t n ≫
        resolutionComparison (relativeGlobalSections f') η n := by
  exact (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv_naturality_right_square
    (resolutionComparison (relativeGlobalSections f) ε n)
    (baseChangeMap φ f f' g w M hM
      (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n)
    ((homologyFunctor (ModuleCat R) _ n).map
        (resolutionSectionsBaseChangeMap φ f f' g w t) ≫
      (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
        (((relativeGlobalSections f').mapHomologicalComplex _).obj L) n).hom)
    (resolutionComparison (relativeGlobalSections f') η n)
    (by
      simpa only [relativeCohomology, Functor.comp_obj, Category.assoc] using
        (resolutionComparison_baseChangeMap φ f f' g w ε η t ht hM
          (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n))

end BaseChange

end Langlands.AlgebraicGeometry.Modules.DerivedSections
