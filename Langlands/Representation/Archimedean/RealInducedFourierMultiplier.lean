import Langlands.Representation.Archimedean.RealLeviDensity
import Langlands.Representation.Archimedean.RealInductionStagesInduce
import Langlands.Representation.Archimedean.RealInducedTorusCore
import Langlands.Representation.Archimedean.RealLeviProducts
import Langlands.Representation.Archimedean.RealTemperedFormProof

/-! # Fourier multipliers after induction in stages -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.InductionStages

open Langlands.LocalFactor.Archimedean RealInducedBlockBound RealInducedTorusCore

private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ

variable {n a r : ℕ}

/-- Move a rotation slot by the offset of the middle block. -/
def shiftSlot (h : a + r ≤ n) (t : Slot r) : Slot n where
  p := a + t.p
  hp := by have ht := t.hp; omega
  α := t.α
  M := t.M
  j := t.j
  x := t.x
  y := t.y
  w := t.w

private theorem withModes_map_shiftSlot (h : a + r ≤ n) (L : List (Slot r)) (J : List ℤ) :
    withModes (L.map (shiftSlot h)) J = (withModes L J).map (shiftSlot h) := by
  induction L generalizing J with
  | nil => cases J <;> rfl
  | cons t L ih =>
    cases J with
    | nil => rfl
    | cons j J =>
      simp only [List.map_cons, withModes, ih]
      rfl

private theorem coeffs_shiftSlot_at_emb (h : a + r ≤ n) (L : List (Slot r))
    (F : G n → ℂ) (κ : G n) (l : G r) :
    coeffs (L.map (shiftSlot h)) F (blockEmb h l * κ) =
      coeffs L (fun x => F (blockEmb h x * κ)) l := by
  induction L generalizing l with
  | nil => rfl
  | cons t L ih =>
    simp only [List.map_cons, coeffs]
    unfold blockFourierCoefficient
    refine intervalIntegral.integral_congr fun θ _ => ?_
    change coeffs (L.map (shiftSlot h)) F
      (blockRotation n (a + t.p) θ * (blockEmb h l * κ)) * _ = _
    rw [← blockEmb_blockRotation h t.hp, ← mul_assoc, ← map_mul, ih]
    rfl

private theorem coeffs_shiftSlot_sliceK {pre ds post : List RealBlock}
    (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
    (L : List (Slot r)) (F : KFin n (pre ++ ds ++ post)) (κ : unitaryCompact ℝ n) :
    coeffs (L.map (shiftSlot h)) F.val κ.val =
      coeffs L (sliceK h ha hr κ F).val 1 := by
  have hm := coeffs_shiftSlot_at_emb h L F.val κ.val (1 : G r)
  rw [map_one, one_mul] at hm
  refine hm.trans (coeffs_congr_of_eqOn ?_ L 1 (one_mem _))
  intro l hl
  rw [sliceK_apply_coe, slice_apply, sliceFactor_of_mem_unitaryCompact hl, one_mul]

/-- An induced Fourier multiplier has the same coefficient weights along the
slots of the embedded middle block. -/
def RealInducedFourierMultiplierStatement : Prop :=
  ∀ {n a r : ℕ} {pre ds es post : List RealBlock}
    (h : a + r ≤ n) (ha : realRank pre = a) (hd : realRank ds = r)
    (he : realRank es = r) (hn : realRank (pre ++ es ++ post) = n)
    (T : KFin r ds →ₗ[ℂ] KFin r es)
    (hT : ∀ k f, T (kRep r ds k f) = kRep r es k (T f))
    (L : List (Slot r)) (W : List ℤ → ℂ),
    (∀ J : List ℤ, J.length = L.length → ∀ v k, k ∈ unitaryCompact ℝ r →
      coeffs (withModes L J) (T v).val k = W J * coeffs (withModes L J) v.val k) →
    ∀ (J : List ℤ), J.length = L.length → ∀ F k, k ∈ unitaryCompact ℝ n →
      coeffs (withModes (L.map (shiftSlot h)) J) (ind h ha he hd hn T hT F).val k =
        W J * coeffs (withModes (L.map (shiftSlot h)) J) F.val k

theorem realInducedFourierMultiplier : RealInducedFourierMultiplierStatement := by
  intro n a r pre ds es post h ha hd he hn T hT L W hW J hJ F k hk
  let κ : unitaryCompact ℝ n := ⟨k, hk⟩
  change coeffs (withModes (L.map (shiftSlot h)) J) (ind h ha he hd hn T hT F).val κ.val =
    W J * coeffs (withModes (L.map (shiftSlot h)) J) F.val κ.val
  rw [withModes_map_shiftSlot, coeffs_shiftSlot_sliceK h ha he _ _ κ,
    coeffs_shiftSlot_sliceK h ha hd _ _ κ, sliceK_ind, hW J hJ _ _ (one_mem _)]

private theorem coeffs_comm_of_disjoint (L M : List (Slot n)) {F : G n → ℂ} (hF : Continuous F)
    (hLM : ∀ t ∈ L, ∀ u ∈ M, t.Disjoint u) :
    coeffs L (coeffs M F) = coeffs M (coeffs L F) := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [coeffs]
    rw [ih (fun s hs => hLM s (List.mem_cons_of_mem t hs)),
      blockFourierCoefficient_coeffs t.j (continuous_coeffs hF L) M (hLM t List.mem_cons_self)]

/-- Coefficient weights multiply for the composition of two operators
whose rotation slots belong to disjoint coordinate blocks. -/
theorem iteratedFourierMultiplier_comp_of_disjoint {ds es fs : List RealBlock}
    (L M : List (Slot n)) (A B : List ℤ → ℂ)
    (hLM : ∀ t ∈ L, ∀ u ∈ M, t.Disjoint u)
    (T : KFin n ds →ₗ[ℂ] KFin n es) (U : KFin n es →ₗ[ℂ] KFin n fs)
    (hT : ∀ J : List ℤ, J.length = L.length → ∀ v k, k ∈ unitaryCompact ℝ n →
      coeffs (withModes L J) (T v).val k = A J * coeffs (withModes L J) v.val k)
    (hU : ∀ J : List ℤ, J.length = M.length → ∀ v k, k ∈ unitaryCompact ℝ n →
      coeffs (withModes M J) (U v).val k = B J * coeffs (withModes M J) v.val k)
    (J : List ℤ) (hJ : J.length = (L ++ M).length) (v : KFin n ds)
    (k : G n) (hk : k ∈ unitaryCompact ℝ n) :
    coeffs (withModes (L ++ M) J) (U (T v)).val k =
      (A (J.take L.length) * B (J.drop L.length)) * coeffs (withModes (L ++ M) J) v.val k := by
  let J₁ := J.take L.length
  let J₂ := J.drop L.length
  have hLength : J.length = L.length + M.length := by simpa using hJ
  have hJ₁ : J₁.length = L.length := by
    dsimp only [J₁]
    rw [List.length_take, hLength, min_eq_left (by omega)]
  have hJ₂ : J₂.length = M.length := by simp [J₂, hLength]
  let L' := withModes L J₁
  let M' := withModes M J₂
  have hModes : withModes (L ++ M) J = L' ++ M' := by
    have he : J₁ ++ J₂ = J := List.take_append_drop L.length J
    exact (congrArg (withModes (L ++ M)) he).symm.trans (RealLeviDensity.withModes_append _ _ _ _ hJ₁)
  have hDisjoint : ∀ t ∈ L', ∀ u ∈ M', t.Disjoint u := by
    intro t ht u hu
    obtain ⟨t₀, ht₀, j, rfl⟩ := mem_withModes ht
    obtain ⟨u₀, hu₀, i, rfl⟩ := mem_withModes hu
    exact hLM t₀ ht₀ u₀ hu₀
  have hTv := RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions (T v).2
  have hv := RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions v.2
  have h1 : ∀ x ∈ unitaryCompact ℝ n,
      coeffs L' (T v).val x = A J₁ * coeffs L' v.val x := hT J₁ hJ₁ v
  have h2 : ∀ x ∈ unitaryCompact ℝ n,
      coeffs M' (U (T v)).val x = B J₂ * coeffs M' (T v).val x := hU J₂ hJ₂ (T v)
  rw [hModes, RealLeviProducts.coeffs_append, RealLeviProducts.coeffs_append,
    RealTemperedForm.coeffs_eq_mul_of_eqOn h2 L' hk,
    coeffs_comm_of_disjoint L' M' hTv hDisjoint,
    RealTemperedForm.coeffs_eq_mul_of_eqOn h1 M' hk,
    ← coeffs_comm_of_disjoint L' M' hv hDisjoint]
  ring

end Langlands.Archimedean.InductionStages
