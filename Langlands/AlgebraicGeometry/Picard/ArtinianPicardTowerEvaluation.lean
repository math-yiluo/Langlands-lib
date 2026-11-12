import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerAlgebraization

/-! # Actual evaluations of the effective Picard tower bundle -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 400000

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation FormalLineBundle

namespace PicardGroupoid.ArtinianPicardTowerEvaluation

open ArtinianPicardSourceStep ArtinianPicardSourceTower ArtinianPicardSourceAdic
open ArtinianPicardTowerFormalSystem ArtinianPicardTowerAlgebraization

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

local notation "C" => limitRing ε hε f M s₀
local notation "εC" => limitAugmentation ε hε f M s₀
local notation "hεC" => limitAugmentation_surjective ε hε f M s₀
local notation "mC" => IsLocalRing.maximalIdeal C
local notation "F" => system ε hε f M s₀

variable {A : ArtinianTest k K} (α : limitRing ε hε f M s₀ →ₐ[k] A.algebra)
  (hα : A.augmentation.comp α = limitAugmentation ε hε f M s₀) (a : ℕ)
  (h : ArtinianAdicEvaluation.IsBound
    (R := limitRing ε hε f M s₀)
    (IsLocalRing.maximalIdeal (limitRing ε hε f M s₀)) (A := A) α a)

/-- The actual map from a selected original tower test to the given test. -/
def stageMap : test ε hε f M s₀ (index ε hε f M s₀ a) ⟶ A :=
  selectedToAdic ε hε f M s₀ a ≫
    LocalAdicArtinianTests.factor (R := C) εC hεC (A := A) α hα a h

/-- The selected tower map factors the original map from the limiting source
exactly, with its original scalar structure. -/
lemma stageMap_projection :
    (ArtinianTest.toAlgHom (stageMap ε hε f M s₀ (A := A) α hα a h)).comp
        (projection ε hε f M s₀ (index ε hε f M s₀ a)) = α := by
  rw [stageMap, ArtinianTest.toAlgHom_comp, AlgHom.comp_assoc,
    selectedToAdic, toAdic_projection]
  exact LocalAdicArtinianTests.factor_projection (R := C) εC hεC (A := A) α hα a h

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
/-- Evaluation through an ordinary adic space equals the original relative
map of the actual finite augmented factor. -/
lemma finiteMap_relative :
    ArtinianFormalPicardFamily.finiteMap (R := C) mC f (A := A) α a h ≫
        adicRelativeMap ε hε f M s₀ a =
      (relativeSpace f).map (ArtinianTest.baseMap
        (LocalAdicArtinianTests.factor (R := C) εC hεC (A := A) α hα a h)) := by
  apply pullback.hom_ext
  · change _ ≫ (relativeProjection f).app _ = _ ≫ (relativeProjection f).app _
    rw [Category.assoc, adicRelativeMap_fst,
      ArtinianFormalPicardFamily.finiteMap_base, (relativeProjection f).naturality]
    rfl
  · rw [Category.assoc, adicRelativeMap_snd, ← Category.assoc,
      ArtinianFormalPicardFamily.finiteMap_projection, relativeSpace_map_snd,
      relativeSpace_map_snd]
    rfl

/-- The formal-system evaluation is the actual pullback of a selected
original tower bundle along the displayed augmented test map. -/
def evaluationIso :
    ArtinianFormalPicardFamily.evaluate (R := C) mC f (A := A) α F a h ≅
      (LineBundle.pullback ((relativeSpace f).map
        (ArtinianTest.baseMap (stageMap ε hε f M s₀ (A := A) α hα a h)))).obj
          (ArtinianPicardTowerFamily.bundle ε hε f M s₀
            (index ε hε f M s₀ a)) := by
  let q := (relativeSpace f).map (ArtinianTest.baseMap
    (LocalAdicArtinianTests.factor (R := C) εC hεC (A := A) α hα a h))
  let t := (relativeSpace f).map
    (ArtinianTest.baseMap (selectedToAdic ε hε f M s₀ a))
  have hqt : q ≫ t = (relativeSpace f).map
      (ArtinianTest.baseMap (stageMap ε hε f M s₀ (A := A) α hα a h)) := by
    dsimp only [q, t, stageMap]
    rw [← Functor.map_comp, ArtinianTest.baseMap_comp]
  exact (LineBundle.pullbackComp
      (ArtinianFormalPicardFamily.finiteMap (R := C) mC f (A := A) α a h)
      (adicRelativeMap ε hε f M s₀ a)).app
        (relativeBundle ε hε f M s₀ a) ≪≫
    eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj
      (relativeBundle ε hε f M s₀ a))
        (finiteMap_relative ε hε f M s₀ (A := A) α hα a h)) ≪≫
    (LineBundle.pullbackComp q t).app _ ≪≫
    eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj
      (ArtinianPicardTowerFamily.bundle ε hε f M s₀
        (index ε hε f M s₀ a))) hqt)

/-- Ordinary pullback of the effective bundle along the original source map
is the displayed actual selected-stage bundle pullback. -/
def effectiveEvaluationIso :
    (LineBundle.pullback ((relativeSpace f).map (affineBaseMap (A := C) (B := A.algebra) α))).obj
        (effectiveBundle ε hε f M s₀) ≅
      (LineBundle.pullback ((relativeSpace f).map
        (ArtinianTest.baseMap (stageMap ε hε f M s₀ (A := A) α hα a h)))).obj
          (ArtinianPicardTowerFamily.bundle ε hε f M s₀
            (index ε hε f M s₀ a)) :=
  ArtinianFormalPicardFamily.algebraizationIso (R := C) mC f (A := A) α F
      (effectiveBundle ε hε f M s₀) (effectiveComparison ε hε f M s₀) a h ≪≫
    evaluationIso ε hε f M s₀ (A := A) α hα a h

end PicardGroupoid.ArtinianPicardTowerEvaluation

end Langlands.AlgebraicGeometry.Picard
