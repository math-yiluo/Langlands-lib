import Langlands.Cohomology.AcyclicResolution.DerivedCompositeIsomorphismProof
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof

/-!
# Actual derived sections along an acyclic pushforward

The canonical composite comparison specialized to scheme modules, with its
coefficient naturality, cohomology formula, and affine quasi-coherent isomorphism.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (h : X ⟶ Y) {R : CommRingCat.{u}} (g : Y ⟶ Spec R)

/-- The actual derived comparison for a module with vanishing positive higher
 direct images along `h`. Its source uses `h ≫ g` and its target uses `g`. -/
def derivedPushforwardComparison (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)) :
    (DerivedPlus.derivedComplex (relativeGlobalSections (h ≫ g)) ⋙
        DerivedCategory.Plus.ι).obj M ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pushforward h).obj M) :=
  derivedCompComparison (relativeGlobalSections g) (relativeGlobalSectionsCompIso h g) M hM

/-- The actual comparison is natural in the coefficient module. -/
@[reassoc]
lemma derivedPushforwardComparison_naturality {M N : X.Modules} (φ : M ⟶ N)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M))
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj N)) :
    (DerivedPlus.derivedComplex (relativeGlobalSections (h ≫ g)) ⋙
        DerivedCategory.Plus.ι).map φ ≫ derivedPushforwardComparison h g N hN =
      derivedPushforwardComparison h g M hM ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
          DerivedCategory.Plus.ι).map ((Scheme.Modules.pushforward h).map φ) :=
  derivedCompComparison_naturality _ _ φ hM hN

/-- Nonnegative cohomology of the specified derived map is the published
 degreewise pushforward comparison, through the specified homology isomorphisms. -/
@[reassoc]
lemma derivedPushforwardComparison_homology (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (derivedPushforwardComparison h g M hM) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections g)
          (injectiveResolution ((Scheme.Modules.pushforward h).obj M)) n).hom =
      (DerivedPlus.homologyIso (relativeGlobalSections (h ≫ g))
        (injectiveResolution M) n).hom ≫ pushforwardComparison h g M hM n :=
  derivedCompComparison_homology _ _ M hM n

/-- Injective pushforward acyclicity makes the actual derived comparison an
 isomorphism for every coefficient with vanishing positive higher direct images. -/
theorem isIso_derivedPushforwardComparison (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)) :
    IsIso (derivedPushforwardComparison h g M hM) :=
  derivedCompositeIsomorphism X.Modules Y.Modules (ModuleCat.{u} R)
    (Scheme.Modules.pushforward h) (relativeGlobalSections g)
    (relativeGlobalSections (h ≫ g)) (relativeGlobalSectionsCompIso h g) M hM
    (fun J hJ q => (pushforwardInjectiveAcyclic X Y h J hJ q).2 R g)

/-- The isomorphism whose hom is the canonical derived pushforward comparison. -/
def derivedPushforwardComparisonIso (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)) :
    (DerivedPlus.derivedComplex (relativeGlobalSections (h ≫ g)) ⋙
        DerivedCategory.Plus.ι).obj M ≅
      (DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pushforward h).obj M) :=
  have := isIso_derivedPushforwardComparison h g M hM
  asIso (derivedPushforwardComparison h g M hM)

@[simp]
lemma derivedPushforwardComparisonIso_hom (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)) :
    (derivedPushforwardComparisonIso h g M hM).hom =
      derivedPushforwardComparison h g M hM := rfl

/-- For affine `h` and quasi-coherent `M`, the actual derived pushforward
 comparison is an isomorphism with no additional acyclicity premise. -/
def affineDerivedPushforwardComparisonIso (hAffine : IsAffineHom h)
    (M : X.Modules) (hQC : M.IsQuasicoherent) :
    (DerivedPlus.derivedComplex (relativeGlobalSections (h ≫ g)) ⋙
        DerivedCategory.Plus.ι).obj M ≅
      (DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pushforward h).obj M) :=
  derivedPushforwardComparisonIso h g M
    (affineQuasicoherentHigherDirectImageVanishing X Y h hAffine M hQC)

/-- The affine isomorphism uses exactly the canonical comparison map. -/
@[simp]
lemma affineDerivedPushforwardComparisonIso_hom (hAffine : IsAffineHom h)
    (M : X.Modules) (hQC : M.IsQuasicoherent) :
    (affineDerivedPushforwardComparisonIso h g hAffine M hQC).hom =
      derivedPushforwardComparison h g M
        (affineQuasicoherentHigherDirectImageVanishing X Y h hAffine M hQC) := rfl

/-- The affine comparison isomorphism is natural in quasi-coherent coefficients. -/
@[reassoc]
lemma affineDerivedPushforwardComparisonIso_hom_naturality (hAffine : IsAffineHom h)
    {M N : X.Modules} (φ : M ⟶ N) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (DerivedPlus.derivedComplex (relativeGlobalSections (h ≫ g)) ⋙
        DerivedCategory.Plus.ι).map φ ≫
        (affineDerivedPushforwardComparisonIso h g hAffine N hN).hom =
      (affineDerivedPushforwardComparisonIso h g hAffine M hM).hom ≫
        (DerivedPlus.derivedComplex (relativeGlobalSections g) ⋙
          DerivedCategory.Plus.ι).map ((Scheme.Modules.pushforward h).map φ) :=
  derivedPushforwardComparison_naturality h g φ
    (affineQuasicoherentHigherDirectImageVanishing X Y h hAffine M hM)
    (affineQuasicoherentHigherDirectImageVanishing X Y h hAffine N hN)

/-- On every nonnegative cohomology object the affine comparison is the
 published pushforward comparison, with acyclicity supplied by affine vanishing. -/
@[reassoc]
lemma affineDerivedPushforwardComparisonIso_hom_homology (hAffine : IsAffineHom h)
    (M : X.Modules) (hQC : M.IsQuasicoherent) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (affineDerivedPushforwardComparisonIso h g hAffine M hQC).hom ≫
        (DerivedPlus.homologyIso (relativeGlobalSections g)
          (injectiveResolution ((Scheme.Modules.pushforward h).obj M)) n).hom =
      (DerivedPlus.homologyIso (relativeGlobalSections (h ≫ g))
        (injectiveResolution M) n).hom ≫
          pushforwardComparison h g M
            (affineQuasicoherentHigherDirectImageVanishing X Y h hAffine M hQC) n :=
  derivedPushforwardComparison_homology h g M
    (affineQuasicoherentHigherDirectImageVanishing X Y h hAffine M hQC) n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
