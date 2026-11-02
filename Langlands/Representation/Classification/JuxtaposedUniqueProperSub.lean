import Langlands.Representation.Classification.JuxtaposedJacquetCover
import Langlands.Representation.Classification.JuxtaposedJacquetPositivity
import Langlands.Representation.Classification.JuxtaposedShuffleDistinct
import Langlands.Representation.Classification.JuxtaposedSupportLattice
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof

/-!
# At most one nonzero proper subrepresentation of `⟨Δ₀⟩ × ⟨Δ₁⟩`

Let `Δ₀` begin at `ν^l ρ` with length `q` and `Δ₁` begin at `ρ` with length `l`, and
let `J` be the normalized Jacquet functor along the uniform shape `(r, …, r)`. The
shuffle count of `J(⟨Δ₀⟩ × ⟨Δ₁⟩)` (a hypothesis) and the inequivalence of distinct
shuffle tensors make `J(⟨Δ₀⟩ × ⟨Δ₁⟩)` multiplicity free. Sending a subrepresentation
to the image of its Jacquet module is strictly monotone (every nonzero step quotient
has a nonzero Jacquet module) and preserves intersections, and every factor other
than the identity shuffle tensor lies in the image for every nonzero
subrepresentation. The support-lattice argument then shows that two
subrepresentations that are neither zero nor everything are equal.
-/

noncomputable section

open Representation CategoryTheory

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear PadicField.TopologicalData CuspidalSupport CuspidalSupport.JacquetLength

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Under the shuffle count, the normalized Jacquet module of `⟨Δ₀⟩ × ⟨Δ₁⟩` along
the uniform shape has a multiplicity-free composition series. -/
theorem hasMultiplicityFreeCompositionSeries_jacquet
    (hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T)
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l) :
    HasMultiplicityFreeCompositionSeries (CuspidalJacquetMultiplicity.upperJacquet T
      (BlockShape.uniform (q + l) ρ.rank ρ.rank_pos) d.induced.obj) := by
  let := T.topology
  have h := hS1 ρ A (l : ℝ) 0 q l d h₂ hA hd hb₀ hl₀ hb₁ hl₁
  obtain ⟨s, hs⟩ := h.1
  refine hasMultiplicityFreeCompositionSeries_of_le_one _ s hs fun τ hτ m hm => ?_
  rw [(h.2 τ.V τ.ρ hτ m).1 hm]
  refine Finite.card_le_one_iff_subsingleton.2 ⟨fun ⟨S, hS, ⟨e⟩⟩ ⟨S', hS', ⟨e'⟩⟩ => ?_⟩
  exact Subtype.ext (eq_of_shuffleTensor_equiv T ρ.rank_pos A hS hS' (e.trans e'.symm))

/-- **At most one nonzero proper subrepresentation.** Assume the shuffle count of
`TwoSegmentSocleShuffleJacquet`, the vanishing of quasicuspidal Jacquet subquotients
along nonassociated Levis, and that the two orders of `ν^a A × ν^b A` are isomorphic
whenever `b + 1 < a`. Then two subrepresentations of `⟨Δ₀⟩ × ⟨Δ₁⟩` that are neither
`⊥` nor `⊤` are equal. -/
theorem eq_of_ne_bot_of_ne_top_induced
    (hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T)
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T ((q + l) * ρ.rank))
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l)
    (hswap : ∀ a b : ℕ, b + 1 < a → letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (b : ℝ), T.segmentFactor A.obj (a : ℝ)]))
    (X Y : letI := T.topology; Subrepresentation d.induced.representation)
    (hX₀ : X ≠ ⊥) (hX₁ : X ≠ ⊤) (hY₀ : Y ≠ ⊥) (hY₁ : Y ≠ ⊤) :
    X = Y := by
  let := T.topology
  let C := BlockShape.uniform (q + l) ρ.rank ρ.rank_pos
  have hπ : IsSmooth d.induced.representation := d.induced.property
  obtain ⟨i, hi⟩ := exists_injective_initShuffle T ρ A hA q l d h₂ hd hb₀ hl₀ hb₁ hl₁
  have hq : 0 < q := hl₀ ▸ (d.segments ⟨0, by omega⟩).length_pos
  have hσ := (glCuspidalTensor p F T ((q + l) * ρ.rank) (Nat.mul_pos (by omega) ρ.rank_pos) C
    (fun k => segmentSupercuspidalFactor F T A
      (shuffleExponent (m := q + l) (initShuffle q l) (l : ℝ) 0 k))).2.2
  have hpos := nontrivial_jacquet_stepQuotient T ρ.rank_pos
    minimalNonzeroJacquet.{uF, max uF uV} hnon
    (FiniteTensor.externalSmoothObject
      (shuffleFactors F T A.obj (q + l) ρ.rank_pos (initShuffle q l) l 0)) hσ i hi
  exact eq_of_ne_bot_of_ne_top (CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj)
    (hasMultiplicityFreeCompositionSeries_jacquet T hS1 ρ A hA q l d h₂ hd hb₀ hl₀ hb₁ hl₁)
    (jacquetImage T C) (jacquetImage_strictMono T C hπ hpos) (jacquetImage_inf T C hπ)
    (fun τ => Nonempty ((FiniteTensor.externalSmoothObject
        (shuffleFactors F T A.obj (q + l) ρ.rank_pos (idShuffle q l) l 0)).representation.Equiv
          τ.ρ))
    (fun _ _ ⟨e⟩ ⟨e'⟩ => ⟨e.symm.trans e'⟩)
    (fun τ hτ hb Z hZ => mem_jordanHolderSupport_jacquetImage_of_ne_id T hS1 ρ A hA q l d h₂
      hd hb₀ hl₀ hb₁ hl₁ hswap τ hτ hb Z hZ)
    hX₀ hX₁ hY₀ hY₁

end Langlands.Classification.JuxtaposedShuffle
