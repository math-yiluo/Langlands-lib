import Langlands.Cohomology.DerivedExactComposition
import Langlands.AlgebraicGeometry.Modules.DerivedPushforwardComparison
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.Cohomology.DerivedPlusNaturality

/-!
# Derived semilinear base change over affine bases

For a commutative square of schemes `g ≫ f = f' ≫ Spec.map φ` with `f : X ⟶ Spec R`,
`f' : X' ⟶ Spec R'` and `φ : R ⟶ R'`, and an `𝒪_X`-module `M` whose pullback `g^* M` has
vanishing higher direct images along `g`, this file constructs the derived base change map
`RΓ_R(X, M) ⟶ φ_* RΓ_{R'}(X', g^* M)` in the derived category of `R`-modules, proves that it is
natural in `M`, and identifies its cohomology with the degreewise base change map.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

section Restrict

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- At a module `M`, `relativeCohomologyRestrictScalarsIso` is the classical comparison
computed with Mathlib's chosen injective resolution of `M`. -/
lemma relativeCohomologyRestrictScalarsIso_app (n : ℕ) (M : X.Modules) :
    (relativeCohomologyRestrictScalarsIso f n).app M =
      DerivedPlus.rightDerivedCompIsoOfResolution (globalSections X)
        (ModuleCat.restrictScalars (structureRingHom f).hom) (relativeGlobalSectionsIso f)
        (injectiveResolution M) n := by
  refine Iso.ext ?_
  exact (Category.comp_id _).trans (DerivedPlus.compIsoOfResolution_id_hom _ _ _ _ _)

end Restrict

section BaseRing

variable {X : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X ⟶ Spec R')

/-- If `f = f' ≫ Spec.map φ`, then `R`-module global sections along `f` are the `R'`-module
global sections along `f'` with scalars restricted along `φ`. -/
def relativeGlobalSectionsBaseRingIso (w : f = f' ≫ Spec.map φ) :
    relativeGlobalSections f' ⋙ ModuleCat.restrictScalars φ.hom ≅ relativeGlobalSections f :=
  Functor.isoWhiskerRight (relativeGlobalSectionsIso f').symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (globalSections X)
      (ModuleCat.restrictScalarsComp' φ.hom (structureRingHom f').hom (structureRingHom f).hom
        (by rw [structureRingHom_eq_comp φ f f' w, CommRingCat.hom_comp])).symm ≪≫
    relativeGlobalSectionsIso f

/-- The identification of global sections is the identity on sections. -/
@[simp]
lemma relativeGlobalSectionsBaseRingIso_hom_app_apply (w : f = f' ≫ Spec.map φ)
    (M : X.Modules) (x : (relativeGlobalSections f').obj M) :
    ((relativeGlobalSectionsBaseRingIso φ f f' w).hom.app M).hom x = x :=
  rfl

/-- The classical comparison for `relativeGlobalSectionsBaseRingIso`, computed with Mathlib's
chosen injective resolution, is the inverse of `relativeCohomologyBaseRingIso`. -/
lemma rightDerivedCompIsoOfResolution_baseRingIso (w : f = f' ≫ Spec.map φ) (M : X.Modules)
    (n : ℕ) :
    DerivedPlus.rightDerivedCompIsoOfResolution (relativeGlobalSections f')
        (ModuleCat.restrictScalars φ.hom) (relativeGlobalSectionsBaseRingIso φ f f' w)
        (injectiveResolution M) n =
      ((relativeCohomologyBaseRingIso φ f f' w n).app M).symm := by
  have e₁ : (relativeCohomologyRestrictScalarsIso f n).hom.app M =
      (DerivedPlus.rightDerivedCompIsoOfResolution (globalSections X)
        (ModuleCat.restrictScalars (structureRingHom f).hom) (relativeGlobalSectionsIso f)
        (injectiveResolution M) n).hom := by
    rw [← Iso.app_hom, relativeCohomologyRestrictScalarsIso_app]
  have e₂ : (relativeCohomologyRestrictScalarsIso f' n).inv.app M =
      (DerivedPlus.rightDerivedCompIsoOfResolution (globalSections X)
        (ModuleCat.restrictScalars (structureRingHom f').hom) (relativeGlobalSectionsIso f')
        (injectiveResolution M) n).inv := by
    rw [← Iso.app_inv, relativeCohomologyRestrictScalarsIso_app]
  refine Iso.ext ?_
  rw [relativeGlobalSectionsBaseRingIso, DerivedPlus.rightDerivedCompIsoOfResolution_hom_comp]
  simp only [relativeCohomologyBaseRingIso, Iso.symm_hom, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.assoc, e₁, e₂]
  rfl

end BaseRing

section BaseChange

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The derived `φ`-semilinear base change map `RΓ_R(X, M) ⟶ φ_* RΓ_{R'}(X', g^* M)` for the
square `g ≫ f = f' ≫ Spec.map φ`: the map induced by the unit `M ⟶ g_* g^* M`, followed by the
inverse of the derived pushforward comparison for `g^* M` and the identification of derived
`R`-module sections along `g ≫ f` with scalar restriction of derived `R'`-module sections
along `f'`. -/
def derivedBaseChangeMap (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M))) :
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj M ⟶
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback g).obj M)) :=
  (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
    (derivedPushforwardComparisonIso g f _ hM).inv ≫
    (DerivedPlus.derivedCompIso (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom)
      (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).inv.app _

/-- The derived base change map is natural in the module. -/
@[reassoc]
theorem derivedBaseChangeMap_naturality {M N : X.Modules} (u : M ⟶ N)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj N))) :
    (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map u ≫
        derivedBaseChangeMap φ f f' g w N hN =
      derivedBaseChangeMap φ f f' g w M hM ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙
            DerivedCategory.Plus.ι).map ((Scheme.Modules.pullback g).map u)) := by
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality u
  have hc := derivedPushforwardComparison_naturality g f ((Scheme.Modules.pullback g).map u) hM hN
  have hc' : (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙
        DerivedCategory.Plus.ι).map
          ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pullback g).map u)) ≫
        (derivedPushforwardComparisonIso g f _ hN).inv =
      (derivedPushforwardComparisonIso g f _ hM).inv ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections (g ≫ f)) ⋙
          DerivedCategory.Plus.ι).map ((Scheme.Modules.pullback g).map u) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hc.symm
  have hi := (DerivedPlus.derivedCompIso (relativeGlobalSections f')
    (ModuleCat.restrictScalars φ.hom) (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)).inv.naturality
      ((Scheme.Modules.pullback g).map u)
  simp only [Functor.id_map, Functor.comp_map] at hu
  simp only [derivedBaseChangeMap, Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc]
  slice_lhs 2 3 => rw [hc']
  slice_lhs 3 4 => rw [hi]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Nonnegative cohomology of the derived base change map is the degreewise base change map
`baseChangeMap`, through the specified homology isomorphisms and the cohomology comparison of
scalar restriction on derived categories. -/
theorem derivedBaseChangeMap_homology (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedBaseChangeMap φ f f' g w M hM) ≫
      (DerivedPlus.mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ.hom) (n : ℤ)).hom.app
        ((DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙ DerivedCategory.Plus.ι).obj
          ((Scheme.Modules.pullback g).obj M)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        (DerivedPlus.homologyIso (relativeGlobalSections f')
          (injectiveResolution ((Scheme.Modules.pullback g).obj M)) n).hom =
    (DerivedPlus.homologyIso (relativeGlobalSections f) (injectiveResolution M) n).hom ≫
      baseChangeMap φ f f' g w M hM
        (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n := by
  have hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)) :=
    fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f
  have hiso := isIso_pushforwardComparison g f ((Scheme.Modules.pullback g).obj M) hM hJ n
  have h₁ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections f)
          (injectiveResolution ((Scheme.Modules.pushforward g).obj
            ((Scheme.Modules.pullback g).obj M))) n).hom =
      (DerivedPlus.homologyIso (relativeGlobalSections f) (injectiveResolution M) n).hom ≫
        (relativeCohomology f n).map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) :=
    DerivedPlus.homologyIso_hom_naturality _ _ _ _ n
  have h₂ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedPushforwardComparisonIso g f _ hM).inv ≫
        (DerivedPlus.homologyIso (relativeGlobalSections (g ≫ f))
          (injectiveResolution ((Scheme.Modules.pullback g).obj M)) n).hom =
      (DerivedPlus.homologyIso (relativeGlobalSections f)
          (injectiveResolution ((Scheme.Modules.pushforward g).obj
            ((Scheme.Modules.pullback g).obj M))) n).hom ≫
        @inv _ _ _ _ (pushforwardComparison g f ((Scheme.Modules.pullback g).obj M) hM n) hiso := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← derivedPushforwardComparison_homology,
      ← Functor.map_comp_assoc, ← derivedPushforwardComparisonIso_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have h₃ := DerivedPlus.derivedCompIso_inv_homology (relativeGlobalSections f')
    (ModuleCat.restrictScalars φ.hom) (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)
    (injectiveResolution ((Scheme.Modules.pullback g).obj M)) n
  rw [rightDerivedCompIsoOfResolution_baseRingIso, Iso.symm_inv, Iso.app_hom] at h₃
  simp only [derivedBaseChangeMap, Functor.map_comp, Category.assoc]
  rw [h₃, reassoc_of% h₂]
  slice_lhs 1 2 => rw [h₁]
  simp only [Category.assoc]
  rfl

end BaseChange

end Langlands.AlgebraicGeometry.Modules.DerivedSections
