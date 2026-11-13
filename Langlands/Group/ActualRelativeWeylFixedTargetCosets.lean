import Langlands.Group.ActualRelativeWeylTransporterCosets

/-! # Selected minimal transporters to a fixed target and their source cosets -/

noncomputable section

namespace Langlands.Group.RelativeWeylIndexing

open RelativeWeyl

universe u v

variable {B : Type u} {G : Type v} [Group G]
  (T : Subgroup G) (L : Finset B → Subgroup G)
  {M : CoxeterMatrix B} (actual : ActualCoxeterSystem T M)
  (I J : Finset B) (S : Set (Weyl T))

/-- Restrict a lift selection to one literal target and a specified set of
Weyl classes. -/
def fixedTargetTransporterSelection
    (K : Finset B) (n : normalizer T)
    (_h : (L I).map (MulAut.conj (n : G) : G →* G) = L K) : Prop :=
  K = J ∧ (QuotientGroup.mk n : Weyl T) ∈ S

variable (hS : ∀ w ∈ S, ∃ n : normalizer T,
  (QuotientGroup.mk n : Weyl T) = w ∧
    (L I).map (MulAut.conj (n : G) : G →* G) = L J)

include hS in
/-- The selected actual transporter image is the literal source-coset image
of the original set, with no invariance premise on that set. -/
theorem actualTransporterSourceCosets_fixedTarget :
    actualTransporterSourceCosets T L I (fixedTargetTransporterSelection T L I J S) =
      (QuotientGroup.mk : Weyl T → Weyl T ⧸ (inclusion T (L I)).range) '' S := by
  ext c
  constructor
  · rintro ⟨w, ⟨K, n, h, hn, hK, hmem⟩, hcw⟩
    exact ⟨w, hn ▸ hmem, hcw⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨n, hn, h⟩ := hS w hw
    exact ⟨w, ⟨J, n, h, hn, rfl, hn.symm ▸ hw⟩, rfl⟩

/-- Keep the Weyl class when placing selected minima for one target in the
varying-target transporter type. -/
def fixedTargetMinimalTransporterEmbedding :
    {w : Weyl T // IsMinimal actual J I w ∧ w ∈ S} ↪
      actualMinimalTransporterPairs T L actual I (fixedTargetTransporterSelection T L I J S) where
  toFun w := ⟨(J, w.val), w.property.1, by
    obtain ⟨n, hn, h⟩ := hS w.val w.property.2
    exact ⟨n, h, hn, rfl, hn.symm ▸ w.property.2⟩⟩
  inj' _ _ h := Subtype.ext (congrArg
    (fun p : actualMinimalTransporterPairs T L actual I
      (fixedTargetTransporterSelection T L I J S) => p.val.2) h)

include hS in
/-- Minimal selected transporters to a fixed target are bounded by the exact
source-coset image of the original selected set. -/
theorem card_fixedTargetMinimalTransporters_le_sourceCosets [Finite (Weyl T)]
    (hZ : ∀ K, centralizer T ≤ L K)
    (hL : Function.Injective L)
    (hIdent : actualLeviWeylIdentification T L actual) :
    Nat.card {w : Weyl T // IsMinimal actual J I w ∧ w ∈ S} ≤
      Nat.card ((QuotientGroup.mk : Weyl T → Weyl T ⧸ (inclusion T (L I)).range) '' S) := by
  let e := (fixedTargetMinimalTransporterEmbedding T L actual I J S hS).trans
    (actualMinimalTransporterCosetEmbedding T L actual I
      (fixedTargetTransporterSelection T L I J S) hZ hL hIdent)
  calc
    _ ≤ Nat.card (actualTransporterSourceCosets T L I
        (fixedTargetTransporterSelection T L I J S)) :=
      Nat.card_le_card_of_injective e e.injective
    _ = _ := by rw [actualTransporterSourceCosets_fixedTarget T L I J S hS]

end Langlands.Group.RelativeWeylIndexing
