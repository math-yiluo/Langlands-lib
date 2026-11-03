import Langlands.Representation.Classification.SegmentSocleCriterionHalvesStatement
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStructureProof
import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Filtration.JordanHolderComparisonProof
import Langlands.Representation.Filtration.LengthTwoMatching

/-!
# Reducibility of a linked pair of segment socles

The reverse-product structure (Ze80 4.6) supplies a composition series of
length two in one order. Two-factor constituent commutativity (Ze80 1.9)
transfers its Jordan–Hölder factors to the other order.
-/

namespace Langlands.Classification

open CategoryTheory

universe uK uG uA uB uF uV

section JordanHolder

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uA} [AddCommGroup V] [Module k V]

/-- An irreducible representation does not have the composition factors of a
representation with a composition series of length two: its own composition
series `0 ⊆ ρ` has one factor. -/
theorem not_isIrreducible_of_haveSameJordanHolderFactors_lengthTwo
    {ρ : Representation k G V} {B : Rep.{uB} k G} (t : ObjectRepFiltration B 2)
    (ht : t.HasSimpleFactors) (h : HaveSameJordanHolderFactors (Rep.of ρ) B) :
    ¬ ρ.IsIrreducible := by
  intro hρ
  obtain ⟨m, s, s', hs, hs', -⟩ := h
  obtain ⟨e₁, -⟩ := jordanHolderSeriesComparison k G (Rep.of ρ) m 1 s (LengthTwo.oneStep ρ) hs
    (LengthTwo.oneStep_hasSimpleFactors bot_covBy_top)
  obtain ⟨e₂, -⟩ := jordanHolderSeriesComparison k G B m 2 s' t hs' ht
  have h₁ := Fintype.card_congr e₁
  have h₂ := Fintype.card_congr e₂
  simp only [Fintype.card_fin] at h₁ h₂
  omega

end JordanHolder

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A normalized product of the socles of two linked segments is reducible
in either order. -/
theorem linkedSegmentSoclePairReducible :
    LinkedSegmentSoclePairReducible.{uF, uV} F T := by
  have hRev := linkedSegmentSocleReverseProductStructure.{uF, uV} F T
  have hComm := twoFactorProductConstituentCommutativity.{uF, max uF uV} F T
  let := T.topology
  intro n d h₂ hs hl
  rcases hl.precedes_or_precedes with hp | hp
  · let σ := d.shape.adjacentSwap 0 (by change 0 + 1 < d.length; omega)
    let d' := d.permute σ
    have hs' : d'.HasSegmentSocles := fun i => hs (σ i)
    let i₀ : Fin d'.length := ⟨0, by change 0 < d.length; omega⟩
    let i₁ : Fin d'.length := ⟨1, by change 1 < d.length; omega⟩
    have h₀ : σ i₀ = i₁ := Equiv.swap_apply_left _ _
    have h₁ : σ i₁ = i₀ := Equiv.swap_apply_right _ _
    have e₀ : d'.segments i₀ = d.segments i₁ := congrArg d.segments h₀
    have e₁ : d'.segments i₁ = d.segments i₀ := congrArg d.segments h₁
    have hp' : (d'.segments i₁).Precedes (d'.segments i₀) := by
      rw [e₀, e₁]
      exact hp
    obtain ⟨-, -, -, -, -, -, -, s, hsimple, -⟩ := hRev n d' h₂ hs' hp'
    have hirr : ∀ i, (d.blocks i).IsIrreducible := fun i => (hs i).choose_spec.2.1
    exact not_isIrreducible_of_haveSameJordanHolderFactors_lengthTwo s hsimple
      (hComm n d.shape h₂ d.blocks hirr)
  · obtain ⟨-, -, -, -, -, -, -, s, hsimple, -⟩ := hRev n d h₂ hs hp
    exact not_isIrreducible_of_haveSameJordanHolderFactors_lengthTwo s hsimple
      (haveSameJordanHolderFactors_self s hsimple)

end Langlands.Classification
