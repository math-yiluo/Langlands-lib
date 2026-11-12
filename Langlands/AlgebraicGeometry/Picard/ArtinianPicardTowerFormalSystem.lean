import Langlands.Algebra.CompleteLocalIdealCofinalityProof
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerFamily
import Langlands.AlgebraicGeometry.Picard.ArtinianFormalPicardFamily

/-! # An actual formal line-bundle system from the Picard source tower -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 400000

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation FormalLineBundle

namespace PicardGroupoid.ArtinianPicardTowerFormalSystem

open ArtinianPicardSourceStep ArtinianPicardSourceTower ArtinianPicardSourceAdic
open ArtinianPicardTowerMaps

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

/-- A tower stage whose projection kernel lies in the specified adic power. -/
def boundIndex (a : ℕ) : ℕ :=
  (exists_adic_bound ε hε f M s₀ Langlands.Algebra.completeLocalIdealCofinality a).choose

lemma boundIndex_bound (a : ℕ) :
    projectionKernel ε hε f M s₀ (boundIndex ε hε f M s₀ a) ≤ mC ^ (a + 1) :=
  (exists_adic_bound ε hε f M s₀ Langlands.Algebra.completeLocalIdealCofinality a).choose_spec

/-- Increasing choices of stages realizing every ordinary adic quotient. -/
def index : ℕ → ℕ :=
  Nat.rec (boundIndex ε hε f M s₀ 0)
    (fun a j ↦ max j (boundIndex ε hε f M s₀ (a + 1)))

lemma index_le_succ (a : ℕ) :
    index ε hε f M s₀ a ≤ index ε hε f M s₀ (a + 1) :=
  Nat.le_max_left _ _

lemma boundIndex_le_index (a : ℕ) :
    boundIndex ε hε f M s₀ a ≤ index ε hε f M s₀ a := by
  cases a with
  | zero => exact le_rfl
  | succ a => exact Nat.le_max_right _ _

lemma index_bound (a : ℕ) :
    projectionKernel ε hε f M s₀ (index ε hε f M s₀ a) ≤ mC ^ (a + 1) :=
  later_bound ε hε f M s₀ (boundIndex_le_index ε hε f M s₀ a)
    (boundIndex_bound ε hε f M s₀ a)

/-- The specified actual augmented map from the selected stage to the adic test. -/
def selectedToAdic (a : ℕ) :
    test ε hε f M s₀ (index ε hε f M s₀ a) ⟶ adicTest ε hε f M s₀ a :=
  toAdic ε hε f M s₀ (index_bound ε hε f M s₀ a)

lemma selectedToAdic_transition (a : ℕ) :
    towerMap ε hε f M s₀ (index_le_succ ε hε f M s₀ a) ≫
        selectedToAdic ε hε f M s₀ a =
      selectedToAdic ε hε f M s₀ (a + 1) ≫
        LocalAdicArtinianTests.transition εC hεC (Nat.le_succ a) := by
  rw [selectedToAdic, selectedToAdic, towerMap_toAdic, toAdic_adicTransition]

/-- The actual bundle on the ordinary relative adic test. -/
def relativeBundle (a : ℕ) :
    LineBundle ((relativeSpace f).obj (ArtinianTest.base (adicTest ε hε f M s₀ a))) :=
  (LineBundle.pullback ((relativeSpace f).map
    (ArtinianTest.baseMap (selectedToAdic ε hε f M s₀ a)))).obj
      (ArtinianPicardTowerFamily.bundle ε hε f M s₀ (index ε hε f M s₀ a))

/-- The tower transitions give an actual isomorphism at consecutive adic tests. -/
def relativeTransition (a : ℕ) :
    (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap
      (LocalAdicArtinianTests.transition εC hεC (Nat.le_succ a))))).obj
        (relativeBundle ε hε f M s₀ (a + 1)) ≅ relativeBundle ε hε f M s₀ a := by
  let q := (relativeSpace f).map
    (ArtinianTest.baseMap (selectedToAdic ε hε f M s₀ a))
  let q' := (relativeSpace f).map
    (ArtinianTest.baseMap (selectedToAdic ε hε f M s₀ (a + 1)))
  let t := (relativeSpace f).map (ArtinianTest.baseMap
    (towerMap ε hε f M s₀ (index_le_succ ε hε f M s₀ a)))
  let d := (relativeSpace f).map (ArtinianTest.baseMap
    (LocalAdicArtinianTests.transition εC hεC (Nat.le_succ a)))
  have hc : d ≫ q' = q ≫ t := by
    dsimp only [q, q', t, d]
    rw [← Functor.map_comp, ← Functor.map_comp,
      ArtinianTest.baseMap_comp, ArtinianTest.baseMap_comp, selectedToAdic_transition]
  exact (LineBundle.pullbackComp d q').app _ ≪≫
    eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj
      (ArtinianPicardTowerFamily.bundle ε hε f M s₀
        (index ε hε f M s₀ (a + 1)))) hc) ≪≫
    ((LineBundle.pullbackComp q t).app _).symm ≪≫
    (LineBundle.pullback q).mapIso
      (ArtinianPicardTowerFamily.transitionIso ε hε f M s₀ (index_le_succ ε hε f M s₀ a))

/-- Map from the ordinary adic thickening of the total space to the original
relative space over the same quotient ring. -/
def adicRelativeMap (a : ℕ) :
    adicSpace (ArtinianFormalPicardFamily.totalMap (R := C) f) mC a ⟶
      (relativeSpace f).obj (ArtinianTest.base (adicTest ε hε f M s₀ a)) :=
  pullback.lift (pullback.snd _ _)
    (FormalLineBundle.adicProjection _ _ a ≫ pullback.snd (affineBase k C).hom f) (by
      have hw := Over.w (affineBaseMap (adicProjection ε hε f M s₀ a))
      change adicBaseProjection mC a ≫ (affineBase k C).hom =
        (ArtinianTest.base (adicTest ε hε f M s₀ a)).hom at hw
      rw [← hw, ← Category.assoc, ← pullback.condition, Category.assoc]
      exact congrArg (fun g ↦ FormalLineBundle.adicProjection
        (ArtinianFormalPicardFamily.totalMap (R := C) f) mC a ≫ g)
          (pullback.condition (f := (affineBase k C).hom) (g := f)))

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
@[reassoc (attr := simp)]
lemma adicRelativeMap_fst (a : ℕ) :
    adicRelativeMap ε hε f M s₀ a ≫
        (relativeProjection f).app (ArtinianTest.base (adicTest ε hε f M s₀ a)) =
      pullback.snd _ _ :=
  pullback.lift_fst _ _ _

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
@[reassoc (attr := simp)]
lemma adicRelativeMap_snd (a : ℕ) :
    adicRelativeMap ε hε f M s₀ a ≫
        pullback.snd (ArtinianTest.base (adicTest ε hε f M s₀ a)).hom f =
      FormalLineBundle.adicProjection _ _ a ≫ pullback.snd (affineBase k C).hom f :=
  pullback.lift_snd _ _ _

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
lemma adicRelativeMap_transition (a : ℕ) :
    adicTransition (ArtinianFormalPicardFamily.totalMap (R := C) f) mC a ≫
        adicRelativeMap ε hε f M s₀ (a + 1) =
      adicRelativeMap ε hε f M s₀ a ≫
        (relativeSpace f).map (ArtinianTest.baseMap
          (LocalAdicArtinianTests.transition εC hεC (Nat.le_succ a))) := by
  apply pullback.hom_ext
  · change _ ≫ (relativeProjection f).app _ = _ ≫ (relativeProjection f).app _
    rw [Category.assoc, adicRelativeMap_fst, Category.assoc,
      (relativeProjection f).naturality]
    simp only [Over.forget_map]
    rw [← Category.assoc, adicRelativeMap_fst]
    rw [adicTransition, pullback.lift_snd]
    rfl
  · rw [Category.assoc, adicRelativeMap_snd, ← Category.assoc,
      adicTransition_projection, Category.assoc, relativeSpace_map_snd,
      adicRelativeMap_snd]

/-- The actual compatible formal line bundles on the unchanged limit ring. -/
def system :
    FormalLineBundleSystem (ArtinianFormalPicardFamily.totalMap (R := C) f) mC where
  obj a := (LineBundle.pullback (adicRelativeMap ε hε f M s₀ a)).obj
    (relativeBundle ε hε f M s₀ a)
  transition a :=
    (LineBundle.pullbackComp _ _).app _ ≪≫
      eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj
        (relativeBundle ε hε f M s₀ (a + 1)))
          (adicRelativeMap_transition ε hε f M s₀ a)) ≪≫
      ((LineBundle.pullbackComp _ _).app _).symm ≪≫
      (LineBundle.pullback (adicRelativeMap ε hε f M s₀ a)).mapIso
        (relativeTransition ε hε f M s₀ a)

end PicardGroupoid.ArtinianPicardTowerFormalSystem

end Langlands.AlgebraicGeometry.Picard
