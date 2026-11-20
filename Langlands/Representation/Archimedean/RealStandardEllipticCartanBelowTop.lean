import Langlands.Representation.Archimedean.RealCartanFilterSupport
import Langlands.Representation.Archimedean.RealCartanPeakTest
import Langlands.Representation.Archimedean.RealStandardEllipticCartanMatrix

/-! # Vanishing below the elliptic rank of a regular real Cartan -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Langlands.Archimedean.RealStandardEllipticCartan

open Langlands.LocalFactor.Archimedean RealInducedStandardBound RealCartanFilterSupport
  RealLeviCompactChart RealCartanPeakTest RealStandardCompactAverage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ

/-- Whether a block contributes a rotation slot. -/
def isInducedBlock : RealBlock → Bool
  | .character _ => false
  | .induced _ => true

private theorem count_induced_positions (ds : List RealBlock) :
    (List.range (realRank ds)).countP (fun p => (realInducedBlockAt ds p).isSome) =
      ds.countP isInducedBlock := by
  induction ds with
  | nil => rfl
  | cons b ds ih =>
    cases b with
    | character c =>
      rw [realRank_cons, RealBlock.rank, Nat.one_add, List.range_succ_eq_map]
      simp only [List.countP_cons, List.countP_map, realInducedBlockAt, Option.isSome_none,
        isInducedBlock, Bool.false_eq_true, ↓reduceIte]
      exact ih
    | induced d =>
      have hr : realRank (.induced d :: ds) = realRank ds + 1 + 1 := by
        simp only [realRank_cons, RealBlock.rank]
        omega
      rw [hr, List.range_succ_eq_map, List.range_succ_eq_map]
      simp only [List.countP_cons, List.countP_map, List.map_cons, List.map_map,
        Nat.succ_eq_add_one, realInducedBlockAt,
        Option.isSome_some, Option.isSome_none, isInducedBlock, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero]
      change (List.range (realRank ds)).countP (fun p => (realInducedBlockAt ds p).isSome) + 1 = _
      rw [ih]

private theorem length_filterMap_eq_count_isSome {α β : Type*} (f : α → Option β)
    (xs : List α) : (xs.filterMap f).length = xs.countP fun x => (f x).isSome := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x <;> simp [h, ih]

/-- The compact Fourier projections have one slot for each original induced block. -/
theorem length_slots_eq_count_induced {ds : List RealBlock} {n : ℕ} (hn : realRank ds = n) :
    (slots ds n).length = ds.countP isInducedBlock := by
  rw [slots, length_filterMap_eq_count_isSome, ← count_induced_positions ds, hn]
  apply List.countP_congr
  intro p _
  cases hd : realInducedBlockAt ds p with
  | none => simp [slotAt, hd]
  | some d =>
    have hp : p + 1 < n := hn ▸ realInducedBlockAt_lt hd
    simp [slotAt, hd, hp]

/-- Counting the columns is independent of how the original list is enumerated. -/
theorem length_slots_ofBlockData {r s n : ℕ} {ds : List RealBlock}
    {d : Fin r → ComplexCharacterData} {b : Fin s → RealCharacterData}
    (hn : realRank ds = n) (hp : ds.Perm (ofBlockData d b)) : (slots ds n).length = r := by
  rw [length_slots_eq_count_induced hn, hp.countP_eq]
  rw [ofBlockData, List.countP_append, List.countP_map, List.countP_map]
  change (List.ofFn d).countP (fun _ => true) + (List.ofFn b).countP (fun _ => false) = r
  simp

/-- At a separated regular source Cartan, the sufficiently concentrated compact tests
retain only the signed low term at equal elliptic rank and vanish below that rank. -/
def RealStandardEllipticCartanBelowTopStatement : Prop :=
  ∀ {n r s r' s' : ℕ} (h : 2 * r + s = n) (x : Coordinates r s),
    x ∈ separatedRegularCoordinates r s →
    ∀ {ds : List RealBlock} {d : Fin r' → ComplexCharacterData} {b : Fin s' → RealCharacterData},
      realRank ds = n → ds.Perm (ofBlockData d b) → r' ≤ r →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        compactTestTrace (compactHaar n) ds (cartanElement h x) (normalizedTest n ε) =
          (-1 : ℂ) ^ r' * compactLowTrace (compactHaar n) ds (cartanElement h x) (normalizedTest n ε) ∧
        (r' < r → compactTestTrace (compactHaar n) ds (cartanElement h x) (normalizedTest n ε) = 0)

theorem realStandardEllipticCartanBelowTop : RealStandardEllipticCartanBelowTopStatement := by
  intro n r s r' s' h x hx ds d b hn hp hrle
  have hs := length_slots_ofBlockData hn hp
  obtain ⟨ha, hr, hsize, hzero, hskew, hpair, hgram, hd, hnormal⟩ :=
    realStandardEllipticCartanMatrix h x hx
  obtain ⟨U, hU, hOne, htrace⟩ := realCartanFilterSupport n ds (cartanLabel h)
    (cartanSquaredRadius x) (cartanElement h x) ha
    (fun _ _ _ hij heq hk => hsize hij heq hk) (fun _ _ hij => hzero hij)
    (fun _ _ hij heq => hskew hij heq) (fun _ _ hij heq => hpair hij heq) hgram hd hnormal
    (by rwa [hs, hr])
  filter_upwards [(realCartanPeakTest n).2 U hU hOne] with ε hε
  obtain ⟨heq, hvanish⟩ := htrace (compactHaar n) (normalizedTest n ε) hε
  exact ⟨by simpa only [hs] using heq, fun hlt => hvanish (by rwa [hs, hr])⟩

theorem tendsto_compactTestTrace_of_lt {n r s r' s' : ℕ} (h : 2 * r + s = n)
    {x : Coordinates r s} (hx : x ∈ separatedRegularCoordinates r s)
    {ds : List RealBlock} {d : Fin r' → ComplexCharacterData} {b : Fin s' → RealCharacterData}
    (hn : realRank ds = n) (hp : ds.Perm (ofBlockData d b)) (hlt : r' < r) :
    Tendsto (compactTestTrace (compactHaar n) ds (cartanElement h x))
      (Filter.map (normalizedTest n) (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  rw [Filter.tendsto_map'_iff]
  apply tendsto_const_nhds.congr'
  filter_upwards [realStandardEllipticCartanBelowTop h x hx hn hp hlt.le] with ε he
  exact (he.2 hlt).symm

end Langlands.Archimedean.RealStandardEllipticCartan
