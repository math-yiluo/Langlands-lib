import Langlands.Representation.Classification.JuxtaposedDecreasingQuotient
import Langlands.Representation.Classification.JuxtaposedUnionDatum
import Langlands.Representation.Filtration.LengthCriterionProof

/-! The union constituent identifies every irreducible quotient of the juxtaposed product. -/

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands.LengthCriterionProof

universe uK uG uW

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uW} [AddCommGroup V] [Module k V]

/-- The actual projection from a representation onto its quotient by an invariant
subspace, in the successive-quotient model with upper subspace equal to top. -/
def quotientTopMap (ρ : Representation k G V) (K : Subrepresentation ρ) :
    ρ.IntertwiningMap (quotientRep K ⊤) where
  toLinearMap := (lower K ⊤).mkQ.comp
    ((LinearMap.id : V →ₗ[k] V).codRestrict
      (⊤ : Subrepresentation ρ).toSubmodule (fun _ => Submodule.mem_top))
  isIntertwining' _ := by ext v; rfl

theorem quotientTopMap_surjective (ρ : Representation k G V) (K : Subrepresentation ρ) :
    Function.Surjective (quotientTopMap ρ K) := by
  intro w
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (lower K ⊤) w
  exact ⟨v.val, rfl⟩

end Langlands.LengthCriterionProof

namespace Langlands.Classification.JuxtaposedShuffle

open CategoryTheory GeneralLinear PadicField.TopologicalData Finset
open LengthCriterionProof (quotientRep quotientTopMap quotientTopMap_surjective)

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Conditional union datum and irreducible-quotient identification for a
juxtaposed pair of actual segment socles. -/
theorem exists_juxtaposedUnionHead
    (hex : SegmentZelevinskyConstituentExistence.{uF,uV} F T)
    {n : ℕ} (d : T.SegmentProductDatum.{uV,uF} n) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hp : (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩))
    (hj : (d.segments ⟨1, by omega⟩).IsJuxtaposed (d.segments ⟨0, by omega⟩)) :
    letI := T.topology
    (d.segments ⟨0, by omega⟩).base =
        (d.segments ⟨1, by omega⟩).base.twist ((d.segments ⟨1, by omega⟩).length : ℝ) ∧
      ∃ (U : T.Segment.{uV, uF}) (I : Option (T.Segment.{uV, uF}))
        (e : T.SegmentProductDatum.{uV, uF} n),
      (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
          (d.segments ⟨1, by omega⟩) U I ∧
        List.ofFn e.segments = U :: I.toList ∧
        e.HasSegmentSocles ∧
        Representation.IsIrreducible e.induced.representation ∧
        e.length = 1 ∧
        (∀ i, (e.segments i).base = (d.segments ⟨1, by omega⟩).base ∧
          (e.segments i).length =
            (d.segments ⟨0, by omega⟩).length + (d.segments ⟨1, by omega⟩).length) ∧
        ∀ K : Subrepresentation d.induced.representation,
          Representation.IsIrreducible (quotientRep K ⊤) →
            Nonempty ((quotientRep K ⊤).Equiv e.induced.representation) := by
  let := T.topology
  have hbase := hj.base_eq_twist_length_of_precedes hp
  refine ⟨hbase, ?_⟩
  have key : ∀ (ρ : CuspidalDatum.{uV,uF} T)
      (A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := ρ.rank)),
      ρ.IsRepresentedBy A → (d.segments ⟨1, by omega⟩).base = ρ →
      ∃ (U : T.Segment.{uV, uF}) (I : Option (T.Segment.{uV, uF}))
        (e : T.SegmentProductDatum.{uV, uF} n),
      (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
          (d.segments ⟨1, by omega⟩) U I ∧
        List.ofFn e.segments = U :: I.toList ∧
        e.HasSegmentSocles ∧
        Representation.IsIrreducible e.induced.representation ∧
        e.length = 1 ∧
        (∀ i, (e.segments i).base = (d.segments ⟨1, by omega⟩).base ∧
          (e.segments i).length =
            (d.segments ⟨0, by omega⟩).length + (d.segments ⟨1, by omega⟩).length) ∧
        ∀ K : Subrepresentation d.induced.representation,
          Representation.IsIrreducible (quotientRep K ⊤) →
            Nonempty ((quotientRep K ⊤).Equiv e.induced.representation) := by
    intro ρ A hA hρ
    obtain ⟨q, hq⟩ : ∃ q, (d.segments ⟨0, by omega⟩).length = q := ⟨_, rfl⟩
    obtain ⟨l, hl⟩ : ∃ l, (d.segments ⟨1, by omega⟩).length = l := ⟨_, rfl⟩
    have hsum : (d.segments ⟨0, by omega⟩).degree +
        (d.segments ⟨1, by omega⟩).degree = n := by
      rcases d with ⟨len, segs, hsum, blocks⟩
      change len = 2 at h₂
      subst len
      simpa [Fin.sum_univ_two] using hsum
    have hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l := by
      simpa only [hρ, hl] using hbase
    have hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0 := by
      rw [hρ, CuspidalDatum.twist_zero]
    have hn : n = (q + l) * ρ.rank := by
      rw [← hsum, Nat.add_mul]
      change (d.segments ⟨0, by omega⟩).length * (d.segments ⟨0, by omega⟩).base.rank +
        (d.segments ⟨1, by omega⟩).length * (d.segments ⟨1, by omega⟩).base.rank = _
      rw [hb₀, hρ, hq, hl]
      rfl
    subst n
    have hpos : 0 < q + l := by
      have := (d.segments ⟨0, by omega⟩).length_pos
      omega
    let U : T.Segment.{uV,uF} := ⟨ρ, q + l, hpos⟩
    have hU : (d.segments ⟨1, by omega⟩).juxtaposedUnion
        (d.segments ⟨0, by omega⟩) = U := by
      simp only [Segment.juxtaposedUnion, hρ, hq, hl, Nat.add_comm]
      rfl
    obtain ⟨π, hπ, hhead⟩ := hex U
    have hirr : π.IsIrreducible := by
      obtain ⟨A', hA', hπ'⟩ := hπ
      exact hπ'.1
    let e := SegmentProductDatum.ofSingleSegment U π (rfl : U.degree = (q + l) * ρ.rank)
    have ε := SegmentProductDatum.ofSingleSegmentInducedEquiv U π
      (rfl : U.degree = (q + l) * ρ.rank)
    obtain ⟨Q, hQ⟩ := exists_surjective_from_decreasing T hex ρ A hA q l d h₂ hd hb₀ hq hb₁ hl
    have hrep := hj.union_replacement hp
    rw [hU] at hrep
    refine ⟨U, none, e, hrep,
      SegmentProductDatum.ofSingleSegment_segments U π rfl,
      SegmentProductDatum.ofSingleSegment_hasSegmentSocles U π rfl hπ,
      SegmentProductDatum.ofSingleSegment_induced_irreducible U π rfl hirr,
      rfl, ?_, ?_⟩
    · intro i
      have hi : e.segments i = U := by
        have hi : i = ⟨0, by change 0 < 1; omega⟩ := by
          apply Fin.ext
          have := i.isLt
          change i.val < 1 at this
          change i.val = 0
          omega
        subst i
        rfl
      rw [hi]
      exact ⟨hρ.symm, hq.symm ▸ hl.symm ▸ rfl⟩
    · intro K hK
      obtain ⟨η⟩ := (hhead A hA).nonempty_equiv_of_quotient_of_surjective Q hQ hK
        (quotientTopMap d.induced.representation K)
        (quotientTopMap_surjective d.induced.representation K)
      exact ⟨η.trans ε.symm⟩
  obtain ⟨A, hA, -⟩ := hd ⟨1, by omega⟩
  exact key _ A hA rfl

end Langlands.Classification.JuxtaposedShuffle
