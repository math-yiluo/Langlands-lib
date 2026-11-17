import Langlands.Automorphic.IsobaricData
import Langlands.Automorphic.ArchimedeanPlaceParameterClasses
import Langlands.LocalFactor.ArchimedeanPairFactor

/-! # Real-place parameters of isobaric constituent data

Enumerate every cuspidal constituent with multiplicity, supply its literal real-place
parameter, and aggregate the block lists up to permutation. This constructs no isobaric
representation and asserts no existence, uniqueness or base-change compatibility.
-/

noncomputable section

open scoped BigOperators

universe uF

namespace Langlands.Automorphic.IsobaricData

open Langlands.Global Langlands.LocalFactor.Archimedean

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- A real-place parameter of constituent data is the permutation closure of the
concatenation of literal parameters of all the constituents, with their multiplicities. -/
def HasRealPlaceParameter (D : IsobaricData F)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock) : Prop :=
  ∃ (b : ℕ) (σ : Fin b → PositiveRankCuspidalClass F),
    Finset.univ.val.map σ = D ∧
    ∃ d : Fin b → List RealBlock,
      (∀ j, (σ j).HasRealPlaceParameter v (d j)) ∧
      ds.Perm ((List.ofFn d).flatten)

private theorem realRank_flatten_ofFn {b : ℕ} (d : Fin b → List RealBlock) :
    realRank ((List.ofFn d).flatten) = ∑ j, realRank (d j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [List.ofFn_succ, List.flatten_cons, realRank_append, Fin.sum_univ_succ, ih]

/-- A real-place parameter has the rank of the constituent data. -/
theorem HasRealPlaceParameter.realRank_eq {D : IsobaricData F}
    {v : {v : NumberField.InfinitePlace F // v.IsReal}} {ds : List RealBlock}
    (h : D.HasRealPlaceParameter v ds) : realRank ds = D.rank := by
  obtain ⟨b, σ, hσ, d, hd, hp⟩ := h
  calc
    realRank ds = realRank ((List.ofFn d).flatten) := (hp.map RealBlock.rank).sum_eq
    _ = ∑ j, realRank (d j) := realRank_flatten_ofFn d
    _ = ∑ j, (σ j).rank := Finset.sum_congr rfl fun j _ => (hd j).realRank_eq
    _ = D.rank := by
      change (Finset.univ.val.map (fun j => (σ j).rank)).sum =
        (D.map PositiveRankCuspidalClass.rank).sum
      rw [← hσ, Multiset.map_map]
      rfl

/-- A permutation of the aggregate block list is also a parameter. -/
theorem HasRealPlaceParameter.of_perm {D : IsobaricData F}
    {v : {v : NumberField.InfinitePlace F // v.IsReal}} {ds es : List RealBlock}
    (h : D.HasRealPlaceParameter v ds) (hp : ds.Perm es) :
    D.HasRealPlaceParameter v es := by
  obtain ⟨b, σ, hσ, d, hd, hds⟩ := h
  exact ⟨b, σ, hσ, d, hd, hp.symm.trans hds⟩

theorem hasRealPlaceParameter_perm_iff {D : IsobaricData F}
    {v : {v : NumberField.InfinitePlace F // v.IsReal}} {ds es : List RealBlock}
    (hp : ds.Perm es) : D.HasRealPlaceParameter v ds ↔ D.HasRealPlaceParameter v es :=
  ⟨fun h => h.of_perm hp, fun h => h.of_perm hp.symm⟩

/-- Empty constituent data have exactly the empty block list as parameter. -/
@[simp]
theorem hasRealPlaceParameter_zero_iff
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock) :
    (0 : IsobaricData F).HasRealPlaceParameter v ds ↔ ds = [] := by
  constructor
  · rintro ⟨b, σ, hσ, d, hd, hp⟩
    have hb : b = 0 := by simpa using congrArg Multiset.card hσ
    subst b
    simpa using hp
  · rintro rfl
    exact ⟨0, Fin.elim0, by simp, Fin.elim0, fun j => Fin.elim0 j, by simp⟩

/-- The singleton relation is the permutation closure of the literal cuspidal relation. -/
theorem hasRealPlaceParameter_ofCuspidal_iff (c : PositiveRankCuspidalClass F)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock) :
    (ofCuspidal c).HasRealPlaceParameter v ds ↔
      ∃ ds', c.HasRealPlaceParameter v ds' ∧ ds.Perm ds' := by
  constructor
  · rintro ⟨b, σ, hσ, d, hd, hp⟩
    have hb : b = 1 := by simpa [ofCuspidal] using congrArg Multiset.card hσ
    subst b
    have hc : σ 0 = c := by
      have hmem : σ 0 ∈ ofCuspidal c :=
        hσ ▸ Multiset.mem_map_of_mem σ (Finset.mem_univ_val 0)
      simpa [ofCuspidal] using hmem
    exact ⟨d 0, by simpa [hc] using hd 0, by simpa using hp⟩
  · rintro ⟨ds', hd, hp⟩
    exact ⟨1, fun _ => c, by simp [ofCuspidal], fun _ => ds', fun _ => hd,
      by simpa using hp⟩

/-- For data with a parameter, emptiness of the data and of the block list agree. -/
theorem HasRealPlaceParameter.eq_zero_iff {D : IsobaricData F}
    {v : {v : NumberField.InfinitePlace F // v.IsReal}} {ds : List RealBlock}
    (h : D.HasRealPlaceParameter v ds) : D = 0 ↔ ds = [] := by
  constructor
  · intro hD
    subst D
    exact (hasRealPlaceParameter_zero_iff v ds).mp h
  · intro hds
    by_contra hD
    have hpos := (rank_pos_iff D).mpr hD
    have hzero : D.rank = 0 := by simpa [hds] using h.realRank_eq.symm
    exact (Nat.ne_of_gt hpos) hzero

end Langlands.Automorphic.IsobaricData
