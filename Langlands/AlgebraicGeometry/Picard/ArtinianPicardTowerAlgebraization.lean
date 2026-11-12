import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerFormalSystem
import Langlands.AlgebraicGeometry.Picard.ProperFormalLineBundleEffectivityProof

/-! # Algebraization and residue identification for the Picard source tower -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 400000

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation FormalLineBundle

namespace PicardGroupoid.ArtinianPicardTowerAlgebraization

open ArtinianPicardSourceStep ArtinianPicardSourceTower ArtinianPicardSourceAdic
open ArtinianPicardTowerFormalSystem

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

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
/-- The limiting augmentation kills the limiting maximal ideal. -/
lemma maximalIdeal_le_augmentation :
    mC ≤ RingHom.ker (εC).toRingHom :=
  le_of_eq (IsLocalRing.ker_eq_maximalIdeal (εC).toRingHom hεC).symm

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
/-- Evaluation at the closed point returns the original relative residue map. -/
lemma residueFiniteMap (a : ℕ)
    (h : ArtinianAdicEvaluation.IsBound mC (A := ArtinianTest.residue k K) εC a) :
    ArtinianFormalPicardFamily.finiteMap mC f
        (A := ArtinianTest.residue k K) εC a h ≫
      adicRelativeMap ε hε f M s₀ a =
        (relativeSpace f).map
          (ArtinianTest.reduction (adicTest ε hε f M s₀ a)) := by
  apply pullback.hom_ext
  · change _ ≫ (relativeProjection f).app _ = _ ≫ (relativeProjection f).app _
    rw [Category.assoc, adicRelativeMap_fst,
      ArtinianFormalPicardFamily.finiteMap_base, (relativeProjection f).naturality]
    rfl
  · rw [Category.assoc, adicRelativeMap_snd, ← Category.assoc,
      ArtinianFormalPicardFamily.finiteMap_projection, relativeSpace_map_snd,
      relativeSpace_map_snd]
    rfl

/-- The formal system retains an actual identification with the original
pointed residue bundle, without a coherence assumption on tower transitions. -/
def residueIdentification :
    M ≅ ArtinianFormalPicardFamily.residueBundle mC f F εC
      (maximalIdeal_le_augmentation ε hε f M s₀) := by
  let b := ArtinianPicardTowerFamily.bundle ε hε f M s₀ (index ε hε f M s₀ 0)
  let q := (relativeSpace f).map
    (ArtinianTest.baseMap (selectedToAdic ε hε f M s₀ 0))
  let r := (relativeSpace f).map
    (ArtinianTest.reduction (adicTest ε hε f M s₀ 0))
  have hqr : r ≫ q = (relativeSpace f).map
      (ArtinianTest.reduction (test ε hε f M s₀ (index ε hε f M s₀ 0))) := by
    dsimp only [r, q]
    rw [← Functor.map_comp, ArtinianTest.reduction_baseMap]
  let e :=
    (LineBundle.pullbackComp
      (ArtinianFormalPicardFamily.finiteMap mC f
        (A := ArtinianTest.residue k K) εC 0
        (ArtinianFormalPicardFamily.residueBound mC εC
          (maximalIdeal_le_augmentation ε hε f M s₀)))
      (adicRelativeMap ε hε f M s₀ 0)).app
        (relativeBundle ε hε f M s₀ 0) ≪≫
    eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj
      (relativeBundle ε hε f M s₀ 0)) (residueFiniteMap ε hε f M s₀ 0 _)) ≪≫
    (LineBundle.pullbackComp r q).app b ≪≫
    eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj b) hqr) ≪≫
    (ArtinianTestDeformations.reductionIso f M
      (family ε hε f M s₀ (index ε hε f M s₀ 0))).symm
  exact e.symm

/-- The tower formal system has an actual compatible algebraization on the
unchanged limiting relative space. -/
lemma exists_algebraization :
    ∃ L : LineBundle ((relativeSpace f).obj (affineBase k C)),
      FormalLineBundleSystem.IsAlgebraization L F := by
  have hp : IsProper (ArtinianFormalPicardFamily.totalMap (R := C) f) := by
    dsimp only [ArtinianFormalPicardFamily.totalMap, relativeProjection]
    infer_instance
  exact properFormalLineBundleEffectivity C _ _ hp F

/-- Choose the actual effective line bundle provided by proper effectivity. -/
def effectiveBundle : LineBundle ((relativeSpace f).obj (affineBase k C)) :=
  (exists_algebraization ε hε f M s₀).choose

/-- The chosen algebraization comes with a comparison respecting every
specified adjacent transition of the formal system. -/
def effectiveComparison :
    FormalLineBundleSystem.Comparison
      (FormalLineBundleSystem.ofLineBundle
        (ArtinianFormalPicardFamily.totalMap (R := C) f) mC
        (effectiveBundle ε hε f M s₀)) F :=
  (exists_algebraization ε hε f M s₀).choose_spec.some

/-- The actual closed point over the original scalar ring. -/
def residuePoint : ArtinianTest.residueBase k K ⟶ affineBase k C :=
  affineBaseMap εC

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
/-- The closed point retains the original actual limiting augmentation map. -/
lemma residuePoint_left :
    (residuePoint ε hε f M s₀).left =
      Spec.map (CommRingCat.ofHom (εC).toRingHom) := rfl

/-- The effective line bundle has the required original actual residue fibre. -/
def effectiveResidueIso :
    ArtinianChartVersality.residueBundle f (effectiveBundle ε hε f M s₀)
      (residuePoint ε hε f M s₀) ≅ M :=
  ArtinianFormalPicardFamily.algebraizationIso mC f
      (A := ArtinianTest.residue k K) εC F
      (effectiveBundle ε hε f M s₀) (effectiveComparison ε hε f M s₀) 0
      (ArtinianFormalPicardFamily.residueBound mC εC
        (maximalIdeal_le_augmentation ε hε f M s₀)) ≪≫
    (residueIdentification ε hε f M s₀).symm

end PicardGroupoid.ArtinianPicardTowerAlgebraization

end Langlands.AlgebraicGeometry.Picard
