import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Good
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Twist
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.FinitePropagation

/-! # Propagating section killing through a quadrant -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}} {K : Type u} [Field K]

/-- Vanishing in one degree at a specified pair of twists. -/
def Vanishes (f : X ⟶ Spec (CommRingCat.of K)) (N₁ N₂ G : X.Modules)
    (i a b : ℕ) : Prop :=
  IsZero ((DerivedSections.relativeCohomology f i).obj ((pairTwist N₁ N₂ a b).obj G))

def swapRightIso (G N P : X.Modules) :
    tensorObj (tensorObj G N) P ≅ tensorObj (tensorObj G P) N :=
  tensorAssociator G N P ≪≫
    (tensorFunctor X).mapIso ((Iso.refl G).prod (tensorComm N P)) ≪≫
      (tensorAssociator G P N).symm

def powerShiftIso (G N : X.Modules) (a d : ℕ) :
    tensorObj (tensorObj G (tensorPow N d)) (tensorPow N a) ≅
      tensorObj G (tensorPow N (a + d)) := by
  simpa only [Nat.add_comm d a] using
    tensorAssociator G (tensorPow N d) (tensorPow N a) ≪≫
      (tensorFunctor X).mapIso ((Iso.refl G).prod (tensorPowAddIso N d a))

def shiftFirstIso (G N₁ N₂ : X.Modules) (a b d : ℕ) :
    (pairTwist N₁ N₂ a b).obj (tensorObj G (tensorPow N₁ d)) ≅
      (pairTwist N₁ N₂ (a + d) b).obj G :=
  (tensorBy (tensorPow N₂ b)).mapIso (powerShiftIso G N₁ a d)

def shiftSecondIso (G N₁ N₂ : X.Modules) (a b d : ℕ) :
    (pairTwist N₁ N₂ a b).obj (tensorObj G (tensorPow N₂ d)) ≅
      (pairTwist N₁ N₂ a (b + d)).obj G :=
  (tensorBy (tensorPow N₂ b)).mapIso
      (swapRightIso G (tensorPow N₂ d) (tensorPow N₁ a)) ≪≫
    powerShiftIso (tensorObj G (tensorPow N₁ a)) N₂ b d

lemma vanishes_step_first (f : X ⟶ Spec (CommRingCat.of K))
    (N₁ N₂ G : X.Modules) (h₁ : IsLocallyFreeRankOne N₁)
    (h₂ : IsLocallyFreeRankOne N₂) (d : ℕ) (s : GlobalSections (tensorPow N₁ d))
    (i a b : ℕ)
    (hK : Vanishes f N₁ N₂ (kernel (twistMul _ s G)) (i + 1) a b)
    (hC : Vanishes f N₁ N₂ (cokernel (twistMul _ s G)) i a b)
    (hG : Vanishes f N₁ N₂ G i a b) :
    Vanishes f N₁ N₂ G i (a + d) b :=
  (isZero_cohomology_target f (pairTwist N₁ N₂ a b)
    (fun S hS => shortExact_pairTwist S hS N₁ N₂ h₁ h₂ a b)
    (twistMul _ s G) i hK hC hG).of_iso
      ((DerivedSections.relativeCohomology f i).mapIso (shiftFirstIso G N₁ N₂ a b d).symm)

lemma vanishes_step_second (f : X ⟶ Spec (CommRingCat.of K))
    (N₁ N₂ G : X.Modules) (h₁ : IsLocallyFreeRankOne N₁)
    (h₂ : IsLocallyFreeRankOne N₂) (d : ℕ) (s : GlobalSections (tensorPow N₂ d))
    (i a b : ℕ)
    (hK : Vanishes f N₁ N₂ (kernel (twistMul _ s G)) (i + 1) a b)
    (hC : Vanishes f N₁ N₂ (cokernel (twistMul _ s G)) i a b)
    (hG : Vanishes f N₁ N₂ G i a b) :
    Vanishes f N₁ N₂ G i a (b + d) :=
  (isZero_cohomology_target f (pairTwist N₁ N₂ a b)
    (fun S hS => shortExact_pairTwist S hS N₁ N₂ h₁ h₂ a b)
    (twistMul _ s G) i hK hC hG).of_iso
      ((DerivedSections.relativeCohomology f i).mapIso (shiftSecondIso G N₁ N₂ a b d).symm)

/-- Regroup the ray in a power of `N` into ordinary powers, with a residue
twist absorbed into the additional line bundle. -/
def seedIso (G N P : X.Modules) (d q r : ℕ) :
    tensorObj (tensorObj G (tensorPow (tensorPow N d) q)) (tensorObj (tensorPow N r) P) ≅
      tensorObj (tensorObj G (tensorPow N (d * q + r))) P :=
  (tensorAssociator (tensorObj G (tensorPow (tensorPow N d) q))
    (tensorPow N r) P).symm ≪≫
  (tensorBy P).mapIso
    ((tensorBy (tensorPow N r)).mapIso
      ((tensorFunctor X).mapIso ((Iso.refl G).prod (tensorPowMulIso N d q))) ≪≫
    tensorAssociator G (tensorPow N (d * q)) (tensorPow N r) ≪≫
    (tensorFunctor X).mapIso ((Iso.refl G).prod (tensorPowAddIso N (d * q) r)))

/-- This assembly is conditional on section killing. All thresholds, residues,
cohomological degrees and tensor rebracketings are discharged here. -/
theorem Good.of_sectionKilling (hkill : SectionKillingStatement.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsNoetherian X] [X.IsSeparated]
    (N₁ N₂ G : X.Modules) (h₁ : IsLocallyFreeRankOne N₁)
    (h₂ : IsLocallyFreeRankOne N₂) [G.IsQuasicoherent] (hG : HasFiniteAffineSections G)
    (e : ℕ) (hGe : HasSupportDimensionLT G e)
    (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (s₁ : GlobalSections (tensorPow N₁ d₁)) (s₂ : GlobalSections (tensorPow N₂ d₂))
    (hs₁ : IsAffineOpen (trivializationOpen (tensorPow N₁ d₁) s₁))
    (hk₁ : Good f N₁ N₂ (kernel (twistMul _ s₁ G)))
    (hc₁ : Good f N₁ N₂ (cokernel (twistMul _ s₁ G)))
    (hk₂ : Good f N₁ N₂ (kernel (twistMul _ s₂ G)))
    (hc₂ : Good f N₁ N₂ (cokernel (twistMul _ s₂ G))) :
    Good f N₁ N₂ G := by
  obtain ⟨k₁, hk₁⟩ := hk₁
  obtain ⟨c₁, hc₁⟩ := hc₁
  obtain ⟨k₂, hk₂⟩ := hk₂
  obtain ⟨c₂, hc₂⟩ := hc₂
  let m := max k₁ (max c₁ (max k₂ c₂))
  let B := m * d₁
  have hmB : m ≤ B := Nat.le_mul_of_pos_right m hd₁
  have hk₁m : k₁ ≤ m := by dsimp [m]; omega
  have hc₁m : c₁ ≤ m := by dsimp [m]; omega
  have hk₂m : k₂ ≤ m := by dsimp [m]; omega
  have hc₂m : c₂ ≤ m := by dsimp [m]; omega
  apply SerrePropagation.exists_uniform_quadrant (Vanishes f N₁ N₂ G) B d₁ d₂ e hd₁ hd₂
  · intro i hi a b ha hb h
    exact vanishes_step_first f N₁ N₂ G h₁ h₂ d₁ s₁ i a b
      (hk₁ a b (by omega) (by omega) (i + 1) (by omega))
      (hc₁ a b (by omega) (by omega) i hi) h
  · intro i hi a b ha hb h
    exact vanishes_step_second f N₁ N₂ G h₁ h₂ d₂ s₂ i a b
      (hk₂ a b (by omega) (by omega) (i + 1) (by omega))
      (hc₂ a b (by omega) (by omega) i hi) h
  · intro i a b hi
    have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle G _ (rankOne_pow N₁ h₁ a)
    have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle
      (tensorObj G (tensorPow N₁ a)) _ (rankOne_pow N₂ h₂ b)
    exact ((hGe.tensor_lineBundle (rankOne_pow N₁ h₁ a)).tensor_lineBundle
      (rankOne_pow N₂ h₂ b)).isZero_relativeCohomology f
        (QuasicoherentLocal.IsAffineLocallyQuasicoherent.of_isQuasicoherent _) i (by omega)
  · intro i hi _ r₁ _ r₂ _
    let P := tensorObj (tensorPow N₁ r₁) (tensorPow N₂ (B + r₂))
    have hP : IsLocallyFreeRankOne P :=
      (rankOne_pow N₁ h₁ r₁).tensor pullbackTensorComparisonIsIso
        (rankOne_pow N₂ h₂ (B + r₂))
    have heq (k : ℕ) : d₁ * (m + k) + r₁ = B + r₁ + k * d₁ := by
      dsimp [B]
      ring
    have hK : ∀ k, IsZero ((DerivedSections.relativeCohomology f (i + 1)).obj
        (tensorObj (tensorObj (kernel (twistMul _ s₁ G))
          (tensorPow (tensorPow N₁ d₁) (m + k))) P)) := by
      intro k
      have h := hk₁ (B + r₁ + k * d₁) (B + r₂) (by omega) (by omega) (i + 1) (by omega)
      rw [← heq k] at h
      exact h.of_iso ((DerivedSections.relativeCohomology f (i + 1)).mapIso
        (seedIso _ N₁ (tensorPow N₂ (B + r₂)) d₁ (m + k) r₁))
    have hC : ∀ k, IsZero ((DerivedSections.relativeCohomology f i).obj
        (tensorObj (tensorObj (cokernel (twistMul _ s₁ G))
          (tensorPow (tensorPow N₁ d₁) (m + k))) P)) := by
      intro k
      have h := hc₁ (B + r₁ + k * d₁) (B + r₂) (by omega) (by omega) i hi
      rw [← heq k] at h
      exact h.of_iso ((DerivedSections.relativeCohomology f i).mapIso
        (seedIso _ N₁ (tensorPow N₂ (B + r₂)) d₁ (m + k) r₁))
    obtain ⟨t, ht⟩ := hkill K X f inferInstance _ (rankOne_pow N₁ h₁ d₁)
      s₁ hs₁ P hP G inferInstance hG m i hi hK hC
    refine ⟨t, ?_⟩
    rw [← heq t]
    exact ht.of_iso ((DerivedSections.relativeCohomology f i).mapIso
      (seedIso G N₁ (tensorPow N₂ (B + r₂)) d₁ (m + t) r₁).symm)

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
