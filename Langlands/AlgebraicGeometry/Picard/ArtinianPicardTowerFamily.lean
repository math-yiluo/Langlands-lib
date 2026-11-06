import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerMaps

/-! # Actual line-bundle transitions along every source-tower reduction -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerFamily

open Langlands.AlgebraicGeometry.Deformation ArtinianPicardSourceStep
open ArtinianTest
open ArtinianPicardSourceTower ArtinianPicardSourceAdic ArtinianPicardTowerMaps

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)

/-- An adjacent arrow factors each specified later-to-earlier test map. -/
private lemma step_composite {n m : ℕ} (h : n ≤ m) :
    step ε hε f M s₀ m ≫ towerMap ε hε f M s₀ h =
      towerMap ε hε f M s₀ (h.trans (Nat.le_succ m)) := by
  rw [step_eq_towerMap, towerMap_comp]

/-- The underlying actual bundle isomorphism of the original pointed transition. -/
private def bundleStepRaw (s : Stage ε f M) :=
  (s.transition ε hε f M).hom.right.iso

/-- The next actual bundle pulls back to the preceding bundle. -/
def bundleStep (s : Stage ε f M) :
    (LineBundle.pullback ((relativeSpace f).map
      (ArtinianTest.baseMap (s.reduction ε hε f M)))).obj
        (s.next ε hε f M).family.right.of ≅ s.family.right.of :=
  bundleStepRaw ε hε f M s

/-- The actual line bundle underlying the pointed family at a tower stage. -/
abbrev bundle (n : ℕ) :
    LineBundle ((relativeSpace f).obj (ArtinianTest.base (test ε hε f M s₀ n))) :=
  (family ε hε f M s₀ n).right.of

/-- Every specified later-to-earlier tower reduction carries an actual bundle transition. -/
lemma hasTransition {n m : ℕ} (hnm : n ≤ m) :
    Nonempty ((LineBundle.pullback ((relativeSpace f).map
      (ArtinianTest.baseMap (towerMap ε hε f M s₀ hnm)))).obj
        (bundle ε hε f M s₀ m) ≅ bundle ε hε f M s₀ n) := by
  induction m, hnm using Nat.le_induction with
  | base =>
    rw [towerMap_refl, ArtinianTest.baseMap_id, CategoryTheory.Functor.map_id]
    exact ⟨(LineBundle.pullbackId _).app _⟩
  | succ m hnm ih =>
    obtain ⟨d⟩ := ih
    have hc : (relativeSpace f).map (ArtinianTest.baseMap (towerMap ε hε f M s₀ hnm)) ≫
        (relativeSpace f).map (ArtinianTest.baseMap (step ε hε f M s₀ m)) =
        (relativeSpace f).map (ArtinianTest.baseMap
          (towerMap ε hε f M s₀ (hnm.trans (Nat.le_succ m)))) := by
      rw [← Functor.map_comp, ArtinianTest.baseMap_comp, step_composite]
    exact ⟨eqToIso (congrArg (fun q => (LineBundle.pullback q).obj
        (bundle ε hε f M s₀ (m + 1))) hc.symm) ≪≫
      ((LineBundle.pullbackComp _ _).app (bundle ε hε f M s₀ (m + 1))).symm ≪≫
      (LineBundle.pullback ((relativeSpace f).map
        (ArtinianTest.baseMap (towerMap ε hε f M s₀ hnm)))).mapIso
          (bundleStep ε hε f M (stage ε hε f M s₀ m)) ≪≫ d⟩

/-- Choose an actual transition isomorphism along each displayed tower arrow. -/
def transitionIso {n m : ℕ} (hnm : n ≤ m) :
    (LineBundle.pullback ((relativeSpace f).map
      (ArtinianTest.baseMap (towerMap ε hε f M s₀ hnm)))).obj
        (bundle ε hε f M s₀ m) ≅ bundle ε hε f M s₀ n :=
  (hasTransition ε hε f M s₀ hnm).some

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerFamily
