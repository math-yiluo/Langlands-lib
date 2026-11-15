import Langlands.Representation.Classification.MoeglinWaldspurgerProductMoves
import Langlands.Representation.Classification.TwoSegmentHeadCommutationProof
import Langlands.Representation.Classification.SegmentProductPermutation

/-!
# Swapping unlinked segment heads in a binary product

A two-block segment product is, up to rank transport, the binary product of its two blocks; with
the published commutation of two unlinked segment heads this gives the swap of the binary
products of two unlinked segment heads.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem castIso_blocks_of_eq {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    {i j : Fin d.length} (h : i = j) : CastIso T (d.blocks i) (d.blocks j) := by
  subst h
  exact CastIso.refl _

/-- A two-block product is the binary product of its blocks, up to rank transport. -/
theorem castIso_induced_two {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (h : d.length = 0 + 2) :
    letI := T.topology
    CastIso T d.induced
      ((T.binaryNormalizedProductFunctor (d.segments (d.shape.headIndex h)).degree
        (d.segments (d.shape.tailIndex h 0)).degree).obj
          (d.blocks (d.shape.headIndex h), d.blocks (d.shape.tailIndex h 0))) := by
  let := T.topology
  obtain ⟨e⟩ := SegmentProductSplit.nonempty_iso_binary d h
  have e₂ := SegmentProductOrderedAssembly.singletonIso (SegmentProductSplit.tail d h) rfl
    ⟨0, Nat.zero_lt_one⟩
  have h1 : CastIso T d.induced
      ((T.binaryNormalizedProductFunctor (d.shape.headRank h) (d.shape.tailRank h)).obj
        (d.blocks (d.shape.headIndex h), (SegmentProductSplit.tail d h).induced)) :=
    (castIso_of_iso e).trans (castIso_generalLinearRankCast _ _).symm
  have h2 : CastIso T (SegmentProductSplit.tail d h).induced
      (d.blocks (d.shape.tailIndex h 0)) :=
    (castIso_of_iso e₂).trans (castIso_generalLinearRankCast _ _).symm
  exact h1.trans ((CastIso.refl _).binary h2)

theorem swap_cast_zero {m : ℕ} (h : m = 0 + 2) (h0 : 0 < m) (h1 : 0 + 1 < m) :
    Equiv.swap (⟨0, h0⟩ : Fin m) ⟨0 + 1, h1⟩ (Fin.cast h.symm (0 : Fin 2)) =
      Fin.cast h.symm ((0 : Fin 1).succ) := by
  subst h
  rfl

theorem swap_cast_one {m : ℕ} (h : m = 0 + 2) (h0 : 0 < m) (h1 : 0 + 1 < m) :
    Equiv.swap (⟨0, h0⟩ : Fin m) ⟨0 + 1, h1⟩ (Fin.cast h.symm ((0 : Fin 1).succ)) =
      Fin.cast h.symm (0 : Fin 2) := by
  subst h
  rfl

/-- **Head swap.** The binary products of the heads of two unlinked segments in the two orders
are isomorphic up to rank transport. -/
theorem castIso_head_swap {Γ κ : T.Segment.{max uF uV, uF}}
    {L : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear κ.degree F.Carrier)}
    (hL : T.IsSegmentHead Γ L) (hA : T.IsSegmentHead κ A) (hun : ¬ Γ.IsLinked κ) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor Γ.degree κ.degree).obj (L, A))
      ((T.binaryNormalizedProductFunctor κ.degree Γ.degree).obj (A, L)) := by
  let := T.topology
  let d := SegmentProductOrderedAssembly.cons Γ L
    (SegmentProductOrderedAssembly.cons κ A SegmentProductOrderedAssembly.empty)
  have hd : d.HasSegmentHeads := by
    intro i
    fin_cases i
    · exact hL
    · exact hA
  have hsw := twoSegmentHeadCommutation.{uF, uV} F T _ d rfl hd hun
  obtain ⟨esw⟩ := hsw
  have h1 := castIso_induced_two d rfl
  have h2 := castIso_induced_two
    (d.permute (d.shape.adjacentSwap 0 (by change 0 + 1 < 2; omega))) rfl
  have hσ0 : (d.shape.adjacentSwap 0 (by change 0 + 1 < 2; omega))
      ((d.permute (d.shape.adjacentSwap 0 (by change 0 + 1 < 2; omega))).shape.headIndex rfl) =
      d.shape.tailIndex rfl 0 := by
    simp only [BlockShape.adjacentSwap, BlockShape.headIndex, BlockShape.tailIndex]
    exact swap_cast_zero rfl _ _
  have hσ1 : (d.shape.adjacentSwap 0 (by change 0 + 1 < 2; omega))
      ((d.permute (d.shape.adjacentSwap 0 (by change 0 + 1 < 2; omega))).shape.tailIndex rfl 0) =
      d.shape.headIndex rfl := by
    simp only [BlockShape.adjacentSwap, BlockShape.headIndex, BlockShape.tailIndex]
    exact swap_cast_one rfl _ _
  have h3 := (castIso_blocks_of_eq d hσ0).binary (castIso_blocks_of_eq d hσ1)
  exact h1.symm.trans ((castIso_of_iso esw).trans (h2.trans h3))

end Langlands.MoeglinWaldspurger.Derivation
