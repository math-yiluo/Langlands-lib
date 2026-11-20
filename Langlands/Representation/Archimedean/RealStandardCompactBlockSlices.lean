import Langlands.Representation.Archimedean.RealLeviProducts

/-! # Real standard membership from compact block slices -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealLeviChart RealLeviSlices
open scoped BigOperators

/-- A principal-series function belongs to the real standard module of the
concatenated list if each compact block slice is the restriction of a
function in that block's real standard module. -/
def RealStandardMembershipFromCompactBlockSlicesStatement : Prop :=
  ∀ {c : ℕ} (dss : Fin c → List RealBlock)
    (f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ),
    f ∈ principalSeries ℝ (∑ j, sz dss j) (realPositionCharacter (flat dss)) →
    (∀ (i : Fin c) (g : Langlands.GeneralLinear (∑ j, sz dss j) ℝ),
      ∃ φ ∈ realStandardModule (sz dss i) (dss i),
        ∀ k : unitaryCompact ℝ (sz dss i), f (emb (sz dss) i k.val * g) = φ k.val) →
    f ∈ realStandardModule (∑ j, sz dss j) (flat dss)

theorem realStandardMembershipFromCompactBlockSlices :
    RealStandardMembershipFromCompactBlockSlicesStatement := by
  intro c dss f hf hs
  refine ⟨hf, ?_⟩
  intro p d hp k hk g
  have hpos := realInducedBlockAt_lt hp
  rw [realRank_flat dss] at hpos
  have hp' : p < ∑ j, sz dss j := lt_trans (Nat.lt_succ_self p) hpos
  obtain ⟨⟨i, a⟩, ha⟩ := finSigmaFinEquiv.surjective (⟨p, hp'⟩ : Fin (∑ j, sz dss j))
  have hpa : start (sz dss) i + a = p := by
    have h := congrArg Fin.val ha
    change (pos (sz dss) i a : ℕ) = p at h
    simpa only [val_pos] using h
  have hd : realInducedBlockAt (dss i) a = some d := by
    rw [← realInducedBlockAt_flat dss i a a.isLt, hpa]
    exact hp
  have ha' : (a : ℕ) + 1 < sz dss i := realInducedBlockAt_lt hd
  obtain ⟨φ, hφ, hφg⟩ := hs i g
  have hrot (θ : ℝ) :
      f (blockRotation (∑ j, sz dss j) p θ * g) =
        φ (blockRotation (sz dss i) a θ) := by
    rw [← hpa, RealLeviProducts.blockRotation_start_add (sz dss) i ha']
    exact hφg ⟨_, blockRotation_mem_unitaryCompact _ _ _⟩
  have hzero := hφ.2 a d hd k hk 1
  unfold blockFourierCoefficient at hzero ⊢
  simpa only [hrot, mul_one] using hzero

end Langlands.Archimedean
