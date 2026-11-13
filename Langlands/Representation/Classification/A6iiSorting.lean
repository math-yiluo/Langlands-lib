import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionProof
import Langlands.Representation.Classification.SegmentSocleProductData

/-!
# Exponent-sorted orderings of segment-head products

Every precedence-ordered product of segment heads is isomorphic to the product of
the same heads reordered by decreasing chosen unitary exponent. This repeats the
sorting step of `orderedSegmentSquareIntegrableConversion`, keeping the reordered
segment datum itself.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Each supplied segment head has a chosen unitary exponent. -/
theorem exists_unitaryExponent {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hh : d.HasSegmentHeads) (i : Fin d.length) :
    letI := T.topology
    T.IsEssentiallySquareIntegrable (d.blocks i).representation ∧
      Nonempty (UnitaryExponentData (T.determinantNorm (d.segments i).degree)
        (d.blocks i).representation) := by
  let := T.topology
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

/-- A precedence-ordered product of segment heads is isomorphic to the product
of the same heads in an order of decreasing chosen unitary exponents. -/
theorem exists_sorted {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (ho : d.IsPrecedenceOrdered) (hh : d.HasSegmentHeads) :
    letI := T.topology
    ∃ (d' : T.SegmentProductDatum.{max uF uV, uF} n)
      (u : ∀ i, UnitaryExponentData (T.determinantNorm (d'.segments i).degree)
        (d'.blocks i).representation),
      d'.multisegment = d.multisegment ∧ d'.HasSegmentHeads ∧
        Antitone (fun i => (u i).exponent) ∧ Nonempty (d.induced ≅ d'.induced) := by
  classical
  let := T.topology
  let u (i : Fin d.length) :
      UnitaryExponentData (T.determinantNorm (d.segments i).degree)
        (d.blocks i).representation := (exists_unitaryExponent F T d hh i).2.some
  let P (σ : Equiv.Perm (Fin d.length)) : Prop :=
    (d.permute σ).IsPrecedenceOrdered ∧ Nonempty (d.induced ≅ (d.permute σ).induced)
  have hP0 : P (Equiv.refl _) := ⟨ho, ⟨Iso.refl _⟩⟩
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
  exact ⟨d.permute σ, fun i => u (σ i), d.permute_multisegment σ, hh.permute σ, hanti, hP.2⟩

/-- Decreasing chosen exponents of segment heads force precedence order. -/
theorem isPrecedenceOrdered_of_antitone {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hh : d.HasSegmentHeads)
    (u : letI := T.topology
      ∀ i, UnitaryExponentData (T.determinantNorm (d.segments i).degree)
        (d.blocks i).representation)
    (hanti : Antitone (fun i => (u i).exponent)) : d.IsPrecedenceOrdered := by
  let := T.topology
  intro i j hij hprec
  have hlt := (linkedSegmentHeadExponentComparison.{uF,uV} F T
    _ _ _ _ (hh i) (hh j) (u i) (u j)).2 hprec
  exact (not_lt_of_ge (hanti hij.le)) hlt

end Langlands.Classification.A6ii
