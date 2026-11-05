import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionStatement
import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Classification.SegmentSpecialEssentialSquareIntegrabilityProof
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.Classification.LinkedSegmentHeadExponentProof
import Langlands.Representation.Classification.AdjacentUnlinkedSegmentSwapProof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Combinatorics.FinitePermutationSortingProof

/-! # Ordered segment products as square-integrable Langlands data

Equip each supplied head with its analytic unitary normalization, then sort
its exponent using actual adjacent unlinked product isomorphisms.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Reorder the supplied segment heads into square-integrable Langlands data,
retaining every block and an actual isomorphism of the full products. -/
theorem orderedSegmentSquareIntegrableConversion :
    OrderedSegmentSquareIntegrableConversion.{uF,uV} F T := by
  classical
  let := T.topology
  have hblock :
      ∀ n (d : T.SegmentProductDatum.{max uF uV, uF} n), d.HasSegmentHeads →
        ∀ i, T.IsEssentiallySquareIntegrable (d.blocks i).representation ∧
          Nonempty (UnitaryExponentData (T.determinantNorm (d.segments i).degree)
            (d.blocks i).representation) := by
    intro n d hh i
    have hesi := segmentSpecialEssentialSquareIntegrability.{uF,uV} F T
      (d.segments i) (d.blocks i) (hh i).isSegmentQuotient
    refine ⟨hesi, ?_⟩
    obtain ⟨s, hs⟩ := hesi
    have hirr : Representation.IsIrreducible
        (realPowerTwist (T.determinantNorm (d.segments i).degree) (-s)
          (d.blocks i).representation) :=
      (isIrreducible_twist_iff _ _).mpr (hh i).choose_spec.2.1
    obtain ⟨form⟩ := glSquareIntegrableUnitarity.{uF, max uF uV}
      p F T (d.segments i).degree
      (d.segments i).degree_pos _ _ hirr hs
    exact ⟨⟨s, form⟩⟩
  intro n _ d ho hh
  let u (i : Fin d.length) :
      UnitaryExponentData (T.determinantNorm (d.segments i).degree)
        (d.blocks i).representation := (hblock n d hh i).2.some
  let P (σ : Equiv.Perm (Fin d.length)) : Prop :=
    (d.permute σ).IsPrecedenceOrdered ∧ Nonempty (d.induced ≅ (d.permute σ).induced)
  have hP0 : P (Equiv.refl _) := by
    exact ⟨ho, ⟨Iso.refl _⟩⟩
  have hPstep : ∀ σ, P σ → ∀ j (h : j + 1 < d.length),
      (u (σ ⟨j, by omega⟩)).exponent < (u (σ ⟨j + 1, h⟩)).exponent →
      P ((Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩).trans σ) := by
    intro σ hP j h hlt
    let d' := d.permute σ
    have hu : ¬ (d'.segments ⟨j, by change j < d.length; omega⟩).IsLinked
        (d'.segments ⟨j + 1, h⟩) := by
      intro hlinked
      have hnp := hP.1 ⟨j, by change j < d.length; omega⟩ ⟨j + 1, h⟩ (by
        change j < j + 1
        omega)
      exact (not_lt_of_ge
        ((linkedSegmentHeadExponentComparison.{uF,uV} F T
          _ _ _ _ (hh _) (hh _) (u _) (u _)).1 hlinked hnp)) hlt
    have horder := hP.1.permute_adjacentSwap j h hu
    obtain ⟨e₁⟩ := hP.2
    obtain ⟨e₂⟩ := adjacentUnlinkedSegmentSwap.{uF,uV} F T n d' (hh.permute σ) j h hu
    exact ⟨horder, ⟨e₁ ≪≫ e₂⟩⟩
  obtain ⟨σ, hP, hanti⟩ :=
    Combinatorics.finitePermutationSorting d.length (fun i => (u i).exponent) P hP0 hPstep
  let e : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n :=
    { shape := (d.permute σ).shape
      blocks := (d.permute σ).blocks
      irreducible := fun i => (hh (σ i)).choose_spec.2.1
      essentiallySquareIntegrable := fun i => (hblock n d hh (σ i)).1
      unitaryExponent := fun i => u (σ i)
      antitone := hanti }
  refine ⟨e, hP.2, σ.symm, ?_⟩
  intro i
  exact d.permute_occurrences σ i

end Langlands.Classification
