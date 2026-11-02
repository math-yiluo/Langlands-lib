import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SegmentDecreasingCuspidalProduct
import Langlands.Representation.Classification.SegmentHeadProductFiniteness
import Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof
import Langlands.Representation.Derivative.RestrictionBridge
import Langlands.Representation.Derivative.TopLine

/-!
# The top derivative of a supplied special head

The published decreasing-induction embedding and BZ77 Theorem 4.11
give nonvanishing. The general top-line construction then supplies an
actual linear equivalence with the complex scalars.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open Langlands Langlands.GeneralLinear Langlands.Classification
open Langlands.PadicField.TopologicalData Langlands.Derivative
open Langlands.HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private theorem nontrivial_top_of_injective
    (hBZ : OrderedCuspidalProductNoDegenerateSubmodules.{uF,uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (hn : 0 < n) :
    letI := T.topology
    ∀ (B : BlockShape n)
      (A : ∀ i : Fin B.length,
        SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)),
      (∀ i j : Fin B.length, i < j →
        (⟨B.size j, (A j).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{uV,uF} (F := F.Carrier) (n := d)) ≠
          ⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (A i).isoClass⟩) →
      ∀ (P : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
        (f : P ⟶ (T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)),
        Function.Injective (SmoothRep.hom f) → Nontrivial P →
        Nontrivial ((generalLinearDerivative T ψ n n le_rfl).obj P) := by
  let _ := T.topology
  cases n with
  | zero => omega
  | succ N =>
    intro B A hord P f hf hP
    let R := generalLinearRestriction.{uF,max uF uV} T N
    let : Nontrivial (R.obj P) := hP
    let g := R.map f
    have hg : Function.Injective (SmoothRep.hom g) := hf
    let U := (SmoothRep.hom g).range
    have hU : U ≠ ⊥ := LevelCalculus.range_ne_bot g hg
    have hD := hBZ ψ N B A hord U hU
    let D := mirabolicDerivativeOfOrder.{uF,max uF uV} T ψ N (N + 1)
      ⟨Nat.zero_lt_succ N, le_rfl⟩
    have hR : Nontrivial (D.obj (R.obj P)) :=
      (LevelCalculus.nontrivial_iff_of_iso
        (D.mapIso (LevelCalculus.isoRange g hg))).mpr hD
    rw [RestrictionBridge.generalLinearDerivative_succ_obj_eq T ψ le_rfl
      ⟨Nat.zero_lt_succ N, le_rfl⟩ P]
    exact hR

/-- The entire top derivative of a supplied special head is nonzero. -/
theorem segmentHeadTopDerivativeNontrivial
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ : Segment.{uV,uF} T) :
    letI := T.topology
    ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π →
      Nontrivial ((generalLinearDerivative T ψ Δ.degree Δ.degree le_rfl).obj π) := by
  let _ := T.topology
  intro π hπ
  have hex := hπ
  obtain ⟨A, hA, _⟩ := hex
  let c := segmentDecreasingCuspidalProduct F T A Δ.length Δ.rank_pos
  let j := hπ.decreasingSocleEmbedding A hA
  obtain ⟨f, hf⟩ :
      ∃ f : π ⟶ (T.normalizedProductInductionFunctor
        (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)).obj
          (fun i => (c.factors i).obj),
        Function.Injective (SmoothRep.hom f) := by
    rw [c.product_eq]
    exact ⟨SmoothRep.ofHom j.val, j.property⟩
  exact nontrivial_top_of_injective T
    (orderedCuspidalProductNoDegenerateSubmodules.{uF,uV} F T) ψ Δ.degree_pos _ c.factors
    c.ordered_no_twist π f hf
    (SupercuspidalTopDerivative.nontrivial_of_isIrreducible
      π.representation hπ.isIrreducible)

private def line_of_positive_rank
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier),
      A.IsIrreducible → IsAdmissible A.representation →
      Nontrivial ((generalLinearDerivative T ψ n n le_rfl).obj A) →
      ((generalLinearDerivative T ψ n n le_rfl).obj A) ≃ₗ[ℂ] ℂ := by
  let _ := T.topology
  cases n with
  | zero => omega
  | succ N => exact topDerivativeLineEquiv T ψ N

/-- An actual linear equivalence from the entire top derivative of a supplied
special head to the complex scalars. No naturality of this choice is asserted. -/
def segmentHeadTopDerivativeLineEquiv
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ : Segment.{uV,uF} T) :
    letI := T.topology
    ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentHead Δ π →
      ((generalLinearDerivative T ψ Δ.degree Δ.degree le_rfl).obj π) ≃ₗ[ℂ] ℂ := by
  let _ := T.topology
  intro π hπ
  exact line_of_positive_rank T ψ Δ.degree Δ.degree_pos π
    hπ.isIrreducible hπ.isAdmissible (segmentHeadTopDerivativeNontrivial T ψ Δ π hπ)

end Langlands.Classification
