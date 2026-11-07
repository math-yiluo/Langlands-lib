import Langlands.Geometry.Building.ApartmentQuotientSemilinearAction
import Langlands.GroupScheme.IntegralModel.UnramifiedIntegralPointAction

/-! # Semilinear permutations of the actual unramified building quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The actual coefficient conjugations form a group action on rational points
of the actual scalar extension. -/
def rationalConjugateAction :
    (L ≃ₐ[k] L) →* MulAut (rationalPoints (baseChanged k L G)) where
  toFun := rationalConjugate k L G
  map_one' := MulEquiv.ext (rationalConjugate_one k L G)
  map_mul' σ τ := MulEquiv.ext (rationalConjugate_mul k L G σ τ)

@[simp] theorem rationalConjugateAction_apply (σ : L ≃ₐ[k] L)
    (g : rationalPoints (baseChanged k L G)) :
    rationalConjugateAction k L G σ g = rationalConjugate k L G σ g := rfl

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.MaximalUnramified

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance extendedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable (C : BuildingData F (baseChanged F (inertiaFixedField F) G))

local instance : Mono C.i.hom.hom.left :=
  mono_of_isMaximalSplitTorus C.isMaximalSplitTorus

local instance : MulAction (normalizerPoints C.i) C.Apartment :=
  inferInstanceAs (MulAction (normalizerPoints C.i) C.apartment.Apartment)

/-- Explicit apartment-level inputs for coefficient conjugation. The point
subgroup compatibility is reduced to the actual zero-depth root filtrations. -/
structure SemilinearApartmentData where
  /-- An action on this same apartment, with all group laws. -/
  apartment : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* Equiv.Perm C.Apartment
  /-- Coefficient conjugation preserves the original normalizer. -/
  normalizer_mem : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (n : normalizerPoints C.i),
    rationalConjugate F (inertiaFixedField F) G σ n.val ∈ normalizerPoints C.i
  /-- It intertwines the original normalizer action on the apartment. -/
  normalizer_smul : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (n : normalizerPoints C.i) (x : C.Apartment),
    apartment σ (n • x) =
      (⟨rationalConjugate F (inertiaFixedField F) G σ n.val,
        normalizer_mem σ n⟩ : normalizerPoints C.i) • apartment σ x
  /-- The actual relative-root index to which a root is sent. -/
  root : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    relativeRoots C.i → relativeRoots C.i
  /-- Coefficient conjugation sends each actual zero-depth root filtration
  into the indexed zero-depth filtration at the transformed point. -/
  filtration_mem : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : C.Apartment) (a : relativeRoots C.i)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)),
    g ∈ C.filtration x a 0 →
      rationalConjugate F (inertiaFixedField F) G σ g ∈
        C.filtration (apartment σ x) (root σ a) 0

namespace SemilinearApartmentData

variable {C} (D : SemilinearApartmentData C)

/-- Preservation of the actual root generators proves sharp-fixer preservation;
no separate sharp-fixer compatibility premise is required. -/
theorem conjugate_mem_sharpFixer
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : C.Apartment) (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hg : g ∈ C.sharpFixer {x}) :
    rationalConjugate F (inertiaFixedField F) G σ g ∈
      C.sharpFixer {D.apartment σ x} := by
  have h : C.sharpFixer {x} ≤
      (C.sharpFixer {D.apartment σ x}).comap
        (rationalConjugate F (inertiaFixedField F) G σ).toMonoidHom := by
    refine iSup_le fun a => ?_
    intro p hp
    change rationalConjugate F (inertiaFixedField F) G σ p ∈
      C.sharpFixer {D.apartment σ x}
    apply C.apartment.rootFixer_le_sharpFixer (D.root σ a) {D.apartment σ x}
    rw [C.apartment.rootFixer_singleton] at hp ⊢
    exact D.filtration_mem σ x a p hp
  exact h hg

/-- The concrete apartment hypotheses supply the data for the existing quotient
and the actual coefficient automorphism action. -/
def quotientActionData :
    ApartmentQuotient.SemilinearActionData C.apartment.sharpFixerFamily
      (rationalConjugateAction F (inertiaFixedField F) G) where
  apartment := D.apartment
  normalizer_mem := D.normalizer_mem
  normalizer_smul := D.normalizer_smul
  subgroup_mem := D.conjugate_mem_sharpFixer

/-- Genuine semilinear permutations of the original upstairs reduced quotient. -/
def action : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →*
    Equiv.Perm C.ReducedBuilding :=
  D.quotientActionData.action

@[simp] theorem action_apartmentMap
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (x : C.Apartment) :
    D.action σ (C.apartmentMap x) = C.apartmentMap (D.apartment σ x) :=
  D.quotientActionData.action_apartment σ x

/-- This is the original rational-point action, intertwined through actual
coefficient conjugation. -/
theorem action_smul (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (z : C.ReducedBuilding) :
    D.action σ (g • z) =
      rationalConjugate F (inertiaFixedField F) G σ g • D.action σ z :=
  D.quotientActionData.action_smul σ g z

end SemilinearApartmentData

end Langlands.Geometry.Building.MaximalUnramified

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison
open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (M : IntegralModel ↥𝒪[F] F G)

private instance extendedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- A supplied unique point fixed by the original extended model image is fixed
by the quotient Galois action constructed from the apartment-level inputs. -/
theorem unramifiedIntegralImage_semilinearAction_eq_of_unique_fixed
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (D : MaximalUnramified.SemilinearApartmentData C)
    (x : C.ReducedBuilding)
    (hx : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
      g ∈ M.baseChangeUnramified.integralPoints → g • x = x)
    (hunique : ∀ y : C.ReducedBuilding,
      (∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
        g ∈ M.baseChangeUnramified.integralPoints → g • y = y) → y = x)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    D.action σ x = x :=
  M.unramifiedIntegralImage_map_eq_of_unique_fixed C σ (D.action σ)
    (D.action_smul σ) x hx hunique

end Langlands.GroupScheme.IntegralModel
