import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Small projected elements from compact representatives and a noncompact section -/

noncomputable section

open Set Filter Topology

universe u v w

namespace Langlands.Global

/-- If a noncompact group has a section into a ring annihilated by `b`, compact
representatives modulo an additive group force nonzero group elements whose
images multiplied by `b` are arbitrarily small. -/
theorem exists_ne_zero_mul_mem_of_compact_section
    {K : Type u} [AddGroup K]
    {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {F : Type w} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (i : K →+ R) (p : R →+ F) (hp : Continuous p)
    (s : F → R) (hps : ∀ x, p (s x) = x)
    (hF : ¬ IsCompact (univ : Set F)) (b : R) (hsb : ∀ x, s x * b = 0)
    (C : Set R) (hC : IsCompact C) (hcover : ∀ a : R, ∃ k, a - i k ∈ C)
    (N : Set R) (hN : N ∈ 𝓝 (0 : R)) :
    ∃ k : K, k ≠ 0 ∧ i k * b ∈ N := by
  classical
  by_contra! hno
  have hpair : {z : R × R | (z.1 - z.2) * b ∈ N} ∈ 𝓝 ((0 : R), (0 : R)) := by
    have hcont : ContinuousAt (fun z : R × R => (z.1 - z.2) * b) (0, 0) :=
      ((continuous_fst.sub continuous_snd).mul_const b).continuousAt
    apply hcont
    simpa using hN
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hpair
  let W := U ∩ V
  have hW : W ∈ 𝓝 (0 : R) := inter_mem hU hV
  obtain ⟨t, _, ht⟩ := hC.elim_nhds_subcover
    (fun c => (fun d : R => d - c) ⁻¹' W)
    (fun c _ => by
      have hcont := (continuous_id.sub continuous_const : Continuous (fun d : R => d - c))
      apply hcont.continuousAt
      simpa using hW)
  choose k hk using fun x : F => hcover (s x)
  let c (x : F) := s x - i (k x)
  have hc (x : F) : c x ∈ C := hk x
  have hcell (x : F) : ∃ j : t, c x - (j : R) ∈ W := by
    obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp (ht (hc x))
    exact ⟨⟨j, hj⟩, hx⟩
  choose cell hcell using hcell
  have hsame (x y : F) (hxy : cell x = cell y) : k x = k y := by
    by_contra hne
    have hsmall : (c x - c y) * b ∈ N := by
      have hx := (hcell x).1
      have hy := (hcell y).2
      rw [← hxy] at hy
      have h := hUV (show (c x - (cell x : R), c y - (cell x : R)) ∈ U ×ˢ V from ⟨hx, hy⟩)
      change ((c x - (cell x : R)) - (c y - (cell x : R))) * b ∈ N at h
      simpa only [sub_sub_sub_cancel_right] using h
    have heq : i (k y - k x) * b = (c x - c y) * b := by
      calc
        i (k y - k x) * b =
            (c x - c y) * b - (s x * b - s y * b) := by
          dsimp [c]
          rw [map_sub]
          ring
        _ = (c x - c y) * b := by rw [hsb, hsb]; ring
    exact hno (k y - k x) (sub_ne_zero.mpr (fun h => hne h.symm)) (heq.symm ▸ hsmall)
  let r (j : t) : F := Classical.epsilon (fun x => cell x = j)
  have hr (x : F) : k x = k (r (cell x)) := by
    apply hsame
    exact (Classical.epsilon_spec (show ∃ y, cell y = cell x from ⟨x, rfl⟩)).symm
  let D : Set F := ⋃ j : t, (fun z : R => p (i (k (r j))) + p z) '' C
  have hD : IsCompact D := isCompact_iUnion fun j =>
    hC.image (continuous_const.add hp)
  apply hF
  apply hD.of_isClosed_subset isClosed_univ
  intro x _
  apply mem_iUnion.mpr
  refine ⟨cell x, c x, hc x, ?_⟩
  rw [← hr x]
  dsimp [c]
  rw [map_sub, hps]
  abel

end Langlands.Global
