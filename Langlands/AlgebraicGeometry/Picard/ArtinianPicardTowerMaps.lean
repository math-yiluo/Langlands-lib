import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceAdic

/-! # The actual inverse diagram of Picard source tests -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerMaps

open Langlands.AlgebraicGeometry.Deformation ArtinianPicardSourceStep
open ArtinianPicardSourceTower ArtinianPicardSourceAdic

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)

/-- The actual augmented map from any later tower test to any earlier one. -/
def towerMap {n m : ℕ} (hnm : n ≤ m) : test ε hε f M s₀ m ⟶ test ε hε f M s₀ n :=
  ArtinianTest.homMk
    (AlgHom.liftOfSurjective (projection ε hε f M s₀ m)
      (projection_surjective ε hε f M s₀ m) (projection ε hε f M s₀ n)
      (projectionKernel_antitone ε hε f M s₀ hnm)) (by
        ext b
        obtain ⟨c, rfl⟩ := projection_surjective ε hε f M s₀ m b
        simp only [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply]
        exact (DFunLike.congr_fun (augmentation_projection ε hε f M s₀ n) c).trans
          (DFunLike.congr_fun (augmentation_projection ε hε f M s₀ m) c).symm)

lemma towerMap_projection {n m : ℕ} (hnm : n ≤ m) :
    (ArtinianTest.toAlgHom (towerMap ε hε f M s₀ hnm)).comp (projection ε hε f M s₀ m) =
      projection ε hε f M s₀ n :=
  AlgHom.liftOfSurjective_comp _ _ _ _

lemma towerMap_surjective {n m : ℕ} (hnm : n ≤ m) :
    Function.Surjective (ArtinianTest.toAlgHom (towerMap ε hε f M s₀ hnm)) :=
  AlgHom.liftOfSurjective_surjective _ _ _ _ (projection_surjective ε hε f M s₀ n)

/-- The original source projections determine each arbitrary-index test arrow uniquely. -/
lemma towerMap_unique {n m : ℕ} (hnm : n ≤ m)
    (q : test ε hε f M s₀ m ⟶ test ε hε f M s₀ n)
    (hq : (ArtinianTest.toAlgHom q).comp (projection ε hε f M s₀ m) =
      projection ε hε f M s₀ n) : q = towerMap ε hε f M s₀ hnm := by
  apply ArtinianTest.hom_ext
  ext b
  obtain ⟨c, rfl⟩ := projection_surjective ε hε f M s₀ m b
  exact (DFunLike.congr_fun hq c).trans
    (DFunLike.congr_fun (towerMap_projection ε hε f M s₀ hnm) c).symm

@[simp] lemma towerMap_refl (n : ℕ) : towerMap ε hε f M s₀ (le_refl n) = 𝟙 _ := by
  symm
  apply towerMap_unique ε hε f M s₀
  rfl

@[reassoc]
lemma towerMap_comp {n m p : ℕ} (hnm : n ≤ m) (hmp : m ≤ p) :
    towerMap ε hε f M s₀ hmp ≫ towerMap ε hε f M s₀ hnm =
      towerMap ε hε f M s₀ (hnm.trans hmp) := by
  apply towerMap_unique ε hε f M s₀
  rw [ArtinianTest.toAlgHom_comp, AlgHom.comp_assoc, towerMap_projection, towerMap_projection]

/-- The arbitrary-index map recovers the original elementary successor reduction. -/
lemma step_eq_towerMap (n : ℕ) :
    step ε hε f M s₀ n = towerMap ε hε f M s₀ (Nat.le_succ n) := by
  apply towerMap_unique ε hε f M s₀
  exact projection_step ε hε f M s₀ n

/-- The original tests and all actual quotient maps form an inverse diagram. -/
def diagram : ℕᵒᵈ ⥤ ArtinianTest k K where
  obj n := test ε hε f M s₀ (OrderDual.ofDual n)
  map h := towerMap ε hε f M s₀ (leOfHom h)
  map_id n := towerMap_refl ε hε f M s₀ (OrderDual.ofDual n)
  map_comp h r := (towerMap_comp ε hε f M s₀ (leOfHom r) (leOfHom h)).symm

/-- Every arbitrary-index reduction commutes with the exact map to a fixed adic test. -/
lemma towerMap_toAdic {n m a : ℕ} (hnm : n ≤ m)
    (h : projectionKernel ε hε f M s₀ n ≤
      IsLocalRing.maximalIdeal (limitRing ε hε f M s₀) ^ (a + 1)) :
    towerMap ε hε f M s₀ hnm ≫ toAdic ε hε f M s₀ h =
      toAdic ε hε f M s₀ (later_bound ε hε f M s₀ hnm h) := by
  apply toAdic_unique ε hε f M s₀
  rw [ArtinianTest.toAlgHom_comp, AlgHom.comp_assoc, towerMap_projection, toAdic_projection]

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerMaps
