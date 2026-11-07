import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Smooth.CompactCompletionTwist

/-!
# Normalization of the actual Levi Jacquet completion

The normalized and unnormalized Jacquet functors to actual Levi points have
identical compact-open averages and compatible-family completion spaces.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance ambientCompletionPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- The actual radical coinvariants with their unnormalized action on Levi points. -/
def leviUnnormalizedJacquetFunctor (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, u, v} ℂ (rationalPoints M) :=
  letI := leviPointTopology l hl
  Jacquet.Localization.smoothFunctor (pointImage (r ≫ p)) 1 (pointImage (l ≫ p))
      (pointImage_le_normalizer p l r hr)
      (Jacquet.Localization.isInvariant_one _ _ (pointImage_le_normalizer p l r hr)) ⋙
    SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl)

/-- Normalization on actual Levi points is the pullback of the intrinsic closed
Haar inverse-half character, on the same coinvariant carrier. -/
theorem leviJacquetFunctor_obj_representation_twist
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation =
      twist ((HaarModulus.closedInverseHalfCharacter (pointImage (r ≫ p))
          (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
          (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr)).comp
            (leviPointsEquiv p l hp hl).toMonoidHom)
        ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).representation := by
  ext m x
  rfl

/-- Normalization does not change the actual Levi compact-open average. -/
theorem leviJacquetFunctor_averageMap_eq
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ K : CompactOpenSubgroup (rationalPoints M),
      Compact.averageMap ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation
          ((leviJacquetFunctor p l r hp hr hl hmul).obj π).isSmooth K.1 K.2 =
        Compact.averageMap
          ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).representation
          ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).isSmooth K.1 K.2 := by
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro K
  exact Compact.averageMap_twist
    ((HaarModulus.closedInverseHalfCharacter (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr)).comp
        (leviPointsEquiv p l hp hl).toMonoidHom)
    ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).representation
    ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).isSmooth
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).isSmooth K.1 K.2
    (CompactCompletion.closedInverseHalfCharacter_compact_le_ker
      (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr)
      (leviPointsEquiv p l hp hl).toMonoidHom (leviPointsEquiv p l hp hl).continuous K)

/-- The normalized and unnormalized actual Levi Jacquet completions are
linearly equivalent by keeping every compact-open component unchanged. -/
def leviJacquetCompletionNormalizationEquiv
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    CompactCompletion.completion
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).isSmooth ≃ₗ[ℂ]
      CompactCompletion.completion
        ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).representation
        ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).isSmooth := by
  letI := leviPointTopology l hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  exact CompactCompletion.closedInverseHalfTwistEquiv
    (pointImage (r ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr)
    (leviPointsEquiv p l hp hl).toMonoidHom (leviPointsEquiv p l hp hl).continuous
    ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).representation
    ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).isSmooth
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).isSmooth

@[simp]
theorem leviJacquetCompletionNormalizationEquiv_apply
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (x : CompactCompletion.completion
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).isSmooth)
      (K : CompactOpenSubgroup (rationalPoints M)),
      (leviJacquetCompletionNormalizationEquiv p l r hp hr hl hmul π x).1 K = x.1 K :=
  fun _ _ => rfl

@[simp]
theorem leviJacquetCompletionNormalizationEquiv_symm_apply
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (x : CompactCompletion.completion
        ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).representation
        ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).isSmooth)
      (K : CompactOpenSubgroup (rationalPoints M)),
      ((leviJacquetCompletionNormalizationEquiv p l r hp hr hl hmul π).symm x).1 K = x.1 K :=
  fun _ _ => rfl

end Langlands.Aubert.General.RepresentedParabolic
