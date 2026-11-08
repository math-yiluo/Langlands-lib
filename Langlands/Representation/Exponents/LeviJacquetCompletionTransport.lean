import Langlands.Representation.Exponents.LeviJacquetCompletionNormalization
import Langlands.Representation.Smooth.CompactCompletionEquiv
import Langlands.Representation.Smooth.CompactCompletionPullback

/-!
# Transport to the normalized actual Levi Jacquet completion

The concrete untwisted coinvariants, trivial-character localization, actual
Levi points, and Haar normalization are compared by explicit equivalences.
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

local instance ambientTransportPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
variable (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
variable (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
variable (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

/-- From the completion of the concrete unnormalized Jacquet action on the Levi
subgroup to the normalized Jacquet completion on actual Levi rational points. -/
def leviJacquetCompletionTransportEquiv
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    CompactCompletion.completion
        (Jacquet.action π.representation (pointImage (r ≫ p)) (pointImage (l ≫ p))
          (pointImage_le_normalizer p l r hr))
        (Jacquet.isSmooth_action π.representation (pointImage (r ≫ p))
          (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr) π.isSmooth) ≃ₗ[ℂ]
      CompactCompletion.completion
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation
        ((leviJacquetFunctor p l r hp hr hl hmul).obj π).isSmooth := by
  letI := leviPointTopology l hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  let hnorm := pointImage_le_normalizer p l r hr
  let hinv := Jacquet.Localization.isInvariant_one (R := ℂ)
    (pointImage (r ≫ p)) (pointImage (l ≫ p)) hnorm
  let hloc := Jacquet.Localization.isSmooth_action π.representation
    (pointImage (r ≫ p)) 1 (pointImage (l ≫ p)) hnorm hinv π.isSmooth
  exact
    (CompactCompletion.equiv
      (Jacquet.isSmooth_action π.representation (pointImage (r ≫ p))
        (pointImage (l ≫ p)) hnorm π.isSmooth) hloc
      (Jacquet.Localization.trivialEquiv π.representation
        (pointImage (r ≫ p)) (pointImage (l ≫ p)) hnorm).symm).trans
      ((CompactCompletion.pullbackEquiv (leviPointsEquiv p l hp hl)
        (Jacquet.Localization.action π.representation (pointImage (r ≫ p)) 1
          (pointImage (l ≫ p)) hnorm hinv) hloc
        ((leviUnnormalizedJacquetFunctor p l r hp hr hl).obj π).isSmooth).trans
        (leviJacquetCompletionNormalizationEquiv p l r hp hr hl hmul π).symm)

/-- The transport formula at each actual Levi compact index. -/
theorem leviJacquetCompletionTransportEquiv_apply
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (x : CompactCompletion.completion
        (Jacquet.action π.representation (pointImage (r ≫ p)) (pointImage (l ≫ p))
          (pointImage_le_normalizer p l r hr))
        (Jacquet.isSmooth_action π.representation (pointImage (r ≫ p))
          (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr) π.isSmooth))
      (J : CompactOpenSubgroup (rationalPoints M)),
      (leviJacquetCompletionTransportEquiv p l r hp hr hl hmul π x).val J =
        (Jacquet.Localization.trivialEquiv π.representation
          (pointImage (r ≫ p)) (pointImage (l ≫ p))
          (pointImage_le_normalizer p l r hr)).symm
            (x.val (CompactCompletion.compactIndexComap
              (leviPointsEquiv p l hp hl).symm J)) :=
  fun _ _ => rfl

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The inverse quotient comparison sends a concrete class to its localized class. -/
theorem leviJacquetCompletionTransport_trivialEquiv_symm_mk
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (v : π) :
    (Jacquet.Localization.trivialEquiv π.representation
      (pointImage (r ≫ p)) (pointImage (l ≫ p))
      (pointImage_le_normalizer p l r hr)).symm
        (Jacquet.mk π.representation (pointImage (r ≫ p)) v) =
      Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 v := by
  exact (Jacquet.Localization.trivialEquiv π.representation
    (pointImage (r ≫ p)) (pointImage (l ≫ p))
    (pointImage_le_normalizer p l r hr)).symm_apply_apply
      (Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 v)

/-- Transport respects the genuine normalized Jacquet map on every component. -/
theorem leviJacquetCompletionTransportEquiv_natural
    (π σ : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (f : π ⟶ σ) :
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (x : CompactCompletion.completion
        (Jacquet.action π.representation (pointImage (r ≫ p)) (pointImage (l ≫ p))
          (pointImage_le_normalizer p l r hr))
        (Jacquet.isSmooth_action π.representation (pointImage (r ≫ p))
          (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr) π.isSmooth))
      (y : CompactCompletion.completion
        (Jacquet.action σ.representation (pointImage (r ≫ p)) (pointImage (l ≫ p))
          (pointImage_le_normalizer p l r hr))
        (Jacquet.isSmooth_action σ.representation (pointImage (r ≫ p))
          (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr) σ.isSmooth)),
      (∀ K : CompactOpenSubgroup (pointImage (l ≫ p)),
        y.val K = Jacquet.map (pointImage (r ≫ p)) (pointImage (l ≫ p))
          (pointImage_le_normalizer p l r hr) (SmoothRep.hom f) (x.val K)) →
      ∀ J : CompactOpenSubgroup (rationalPoints M),
        (leviJacquetCompletionTransportEquiv p l r hp hr hl hmul σ y).val J =
          SmoothRep.hom ((leviJacquetFunctor p l r hp hr hl hmul).map f)
            ((leviJacquetCompletionTransportEquiv p l r hp hr hl hmul π x).val J) := by
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro x y hxy J
  rw [leviJacquetCompletionTransportEquiv_apply,
    leviJacquetCompletionTransportEquiv_apply, hxy]
  obtain ⟨v, hv⟩ := Jacquet.mk_surjective π.representation (pointImage (r ≫ p))
    (x.val (CompactCompletion.compactIndexComap (leviPointsEquiv p l hp hl).symm J))
  rw [← hv, Jacquet.map_mk,
    leviJacquetCompletionTransport_trivialEquiv_symm_mk p l r hr σ,
    leviJacquetCompletionTransport_trivialEquiv_symm_mk p l r hr π]
  rfl

end Langlands.Aubert.General.RepresentedParabolic
