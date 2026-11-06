import Langlands.Representation.RankinSelberg.GroupedLFactorProduct

/-! # Products over equal-exponent Langlands groups -/

noncomputable section

namespace Langlands.RankinSelberg

open CategoryTheory MeasureTheory HarmonicAnalysis GeneralLinear Polynomial
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

section Grouping

variable (F : PadicField.{uF} p)

local instance groupedDataTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

theorem normalizedProductInduction_equiv_iff {n : ℕ} (B : BlockShape n)
    (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Nonempty (((F.canonicalTopologicalData.normalizedProductInductionFunctor B).obj
      A).representation.Equiv ρ) ↔
      Nonempty ((F.canonicalNormalizedProductInduced B
        (fun i => (A i).representation)).Equiv ρ) := Iff.rfl

/-- The part of an actual equal-exponent grouping used in the factor formula. -/
structure SquareIntegrableFactorGrouping {n : ℕ}
    (d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData n) where
  normalized_squareIntegrable : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable
    (F.canonicalTopologicalData.segmentFactor (d.blocks i) (-d.exponent i)).representation
  tempered : TemperedLanglandsDatum.{uV, uF} F.canonicalTopologicalData n
  fiberMap : Fin d.shape.length → Fin tempered.shape.length
  exponent_eq : ∀ i, d.exponent i = tempered.exponent (fiberMap i)
  shape : ∀ j, BlockShape (tempered.shape.size j)
  indexEquiv : ∀ j, Fin (shape j).length ≃
    {i : Fin d.shape.length // fiberMap i = j}
  rank_eq : ∀ j k, (shape j).size k = d.shape.size (indexEquiv j k).val
  blockEquiv : ∀ j, Nonempty
    (((F.canonicalTopologicalData.normalizedProductInductionFunctor (shape j)).obj
      (fun k => (rank_eq j k).symm ▸ F.canonicalTopologicalData.segmentFactor
        (d.blocks (indexEquiv j k).val) (-d.exponent (indexEquiv j k).val))).representation.Equiv
      (tempered.blocks j).representation)
  inducedIso : Nonempty (d.induced ≅ tempered.standardModule)

namespace SquareIntegrableFactorGrouping

variable {F} {n : ℕ}
  {d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData n}
  (g : SquareIntegrableFactorGrouping F d)

/-- The cast unitarily normalized blocks of one group. -/
def normalizedBlocks (j : Fin g.tempered.shape.length) :
    ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((g.shape j).size k) F.Carrier) :=
  fun k => (g.rank_eq j k).symm ▸ F.canonicalTopologicalData.segmentFactor
    (d.blocks (g.indexEquiv j k).val) (-d.exponent (g.indexEquiv j k).val)

theorem normalizedBlocks_hypotheses (j : Fin g.tempered.shape.length)
    (k : Fin (g.shape j).length) :
    Representation.IsIrreducible (g.normalizedBlocks j k).representation ∧
      F.canonicalTopologicalData.IsSquareIntegrable (g.normalizedBlocks j k).representation ∧
      IsUnitarizable (g.normalizedBlocks j k).representation := by
  exact (Classification.RankIso.block_iff
    (Classification.RankIso.cast (g.rank_eq j k).symm
      (F.canonicalTopologicalData.segmentFactor
        (d.blocks (g.indexEquiv j k).val) (-d.exponent (g.indexEquiv j k).val)))).mp
    (Classification.normalized_block_of_isSquareIntegrable d _
      (g.normalized_squareIntegrable _))

/-- The indices of all groups together are exactly the original indices. -/
def originalIndexEquiv : (Σ j, Fin (g.shape j).length) ≃ Fin d.shape.length :=
  (Equiv.sigmaCongrRight g.indexEquiv).trans (Equiv.sigmaFiberEquiv g.fiberMap)

@[simp]
theorem originalIndexEquiv_apply (j : Fin g.tempered.shape.length)
    (k : Fin (g.shape j).length) :
    g.originalIndexEquiv ⟨j, k⟩ = (g.indexEquiv j k).val := rfl

theorem group_exponent_eq (j : Fin g.tempered.shape.length)
    (k : Fin (g.shape j).length) :
    g.tempered.exponent j = d.exponent (g.indexEquiv j k).val := by
  rw [g.exponent_eq, (g.indexEquiv j k).property]

end SquareIntegrableFactorGrouping

/-- Extract the factor-formula witnesses from the equal-exponent grouping
statement, keeping the actual block and total-induction isomorphisms. -/
theorem exists_squareIntegrableFactorGrouping
    (H : Classification.SquareIntegrableEqualExponentGrouping.{uF, uV}
      F F.canonicalTopologicalData)
    {n : ℕ} (hn : 0 < n)
    (d : SquareIntegrableLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData n) :
    Nonempty (SquareIntegrableFactorGrouping F d) := by
  classical
  obtain ⟨hsi, t, q, _, _, hexp, hblocks, hind⟩ := H n hn d
  choose C e h _ hIso using hblocks
  refine ⟨{
    normalized_squareIntegrable := hsi
    tempered := t
    fiberMap := q
    exponent_eq := hexp
    shape := C
    indexEquiv := e
    rank_eq := h
    blockEquiv := ?_
    inducedIso := hind }⟩
  intro j
  obtain ⟨E⟩ := hIso j
  exact ⟨SmoothRep.equivOfIso E⟩

/-- Choose an actual factor grouping from the explicit grouping premise. -/
def squareIntegrableFactorGrouping
    (H : Classification.SquareIntegrableEqualExponentGrouping.{uF, uV}
      F F.canonicalTopologicalData)
    {n : ℕ} (hn : 0 < n)
    (d : SquareIntegrableLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData n) :
    SquareIntegrableFactorGrouping F d :=
  Classical.choice (exists_squareIntegrableFactorGrouping F H hn d)

end Grouping

section Factors

variable (F : PadicField.{uF} p)

local instance groupedFactorTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {m n : ℕ}
  {d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData m}
  {e : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData n}
  (g : SquareIntegrableFactorGrouping F d) (h : SquareIntegrableFactorGrouping F e)

set_option maxHeartbeats 800000 in
/-- The L-polynomial of a pair of twisted tempered groups is the product of
the L-polynomials of all pairs of their original square-integrable blocks. -/
theorem SquareIntegrableFactorGrouping.pairProduct
    (H : TemperedLFactorStatement.{uF, uV, uW})
    (a : Fin g.tempered.shape.length) (b : Fin h.tempered.shape.length) :
    ∃ (P : ℂ[X])
      (Q : Fin (g.shape a).length → Fin (h.shape b).length → ℂ[X]),
      IsPadicRankLPolynomial F ψ ν.val
        (F.canonicalTopologicalData.twistedBlocks g.tempered.shape
          g.tempered.blocks g.tempered.exponent a).representation
        (F.canonicalTopologicalData.twistedBlocks h.tempered.shape
          h.tempered.blocks h.tempered.exponent b).representation P ∧
      (∀ k l, IsPadicRankLPolynomial F ψ ν.val
        (d.blocks (g.indexEquiv a k).val).representation
        (e.blocks (h.indexEquiv b l).val).representation (Q k l)) ∧
      P = ∏ k, ∏ l, Q k l := by
  have ha := (normalizedProductInduction_equiv_iff F (g.shape a)
    (g.normalizedBlocks a) (g.tempered.blocks a).representation).mp (g.blockEquiv a)
  have hb := (normalizedProductInduction_equiv_iff F (h.shape b)
    (h.normalizedBlocks b) (h.tempered.blocks b).representation).mp (h.blockEquiv b)
  obtain ⟨ea⟩ := ha
  obtain ⟨eb⟩ := hb
  obtain ⟨P, Q, hP, hQ, hprod⟩ := H.commonRealTwistsOfEquiv F ψ ν
    (g.tempered.shape.positive a) (h.tempered.shape.positive b) (g.shape a) (h.shape b)
    (fun k => (g.normalizedBlocks a k).representation)
    (fun l => (h.normalizedBlocks b l).representation)
    (fun k => (g.normalizedBlocks_hypotheses a k).1)
    (fun k => (g.normalizedBlocks_hypotheses a k).2.1)
    (fun l => (h.normalizedBlocks_hypotheses b l).1)
    (fun l => (h.normalizedBlocks_hypotheses b l).2.1)
    (γ := (g.tempered.blocks a).representation)
    (δ := (h.tempered.blocks b).representation)
    ea eb
    (g.tempered.exponent a) (h.tempered.exponent b)
  refine ⟨P, Q, hP, ?_, hprod⟩
  intro k l
  exact (isPadicRankLPolynomial_cast_normalized_twist_iff F ψ ν
    (g.rank_eq a k) (h.rank_eq b l)
    (d.blocks (g.indexEquiv a k).val) (e.blocks (h.indexEquiv b l).val)
    (g.group_exponent_eq a k) (h.group_exponent_eq b l) (Q k l)).mp (hQ k l)

end Factors

section TotalProduct

variable (F : PadicField.{uF} p)

local instance groupedTotalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t : ℕ}
  {d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1)}
  {e : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1)}
  (g : SquareIntegrableFactorGrouping F d) (h : SquareIntegrableFactorGrouping F e)

/-- Combine the Langlands-type formula with all group-pair computations and
reindex the result by the original square-integrable block indices. -/
theorem SquareIntegrableFactorGrouping.product
    (H : TemperedLFactorStatement.{uF, uV, uW})
    (HL : LanglandsTypeLFactorStatement.{uF, uV, uW}) :
    ∃ (P : ℂ[X]) (Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val g.tempered.standardModule.representation
        h.tempered.standardModule.representation P ∧
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val
        (d.blocks i).representation (e.blocks j).representation (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j := by
  classical
  obtain ⟨P, S, hP, hS, hprod⟩ := HL p F ψ ν r t g.tempered h.tempered
  choose Pg Qg hPg hQg hprodg using fun a b => g.pairProduct F ψ ν h H a b
  let Q := groupedPolynomial g.originalIndexEquiv h.originalIndexEquiv Qg
  refine ⟨P, Q, hP, ?_, ?_⟩
  · intro i j
    obtain ⟨⟨a, k⟩, rfl⟩ := g.originalIndexEquiv.surjective i
    obtain ⟨⟨b, l⟩, rfl⟩ := h.originalIndexEquiv.surjective j
    change IsPadicRankLPolynomial F ψ ν.val
      (d.blocks (g.indexEquiv a k).val).representation
      (e.blocks (h.indexEquiv b l).val).representation
      (groupedPolynomial g.originalIndexEquiv h.originalIndexEquiv Qg
        (g.originalIndexEquiv ⟨a, k⟩) (h.originalIndexEquiv ⟨b, l⟩))
    rw [groupedPolynomial_apply]
    exact hQg a b k l
  · calc
      P = ∏ a, ∏ b, S a b := hprod
      _ = ∏ a, ∏ b, ∏ k, ∏ l, Qg a b k l := by
        apply Finset.prod_congr rfl
        intro a _
        apply Finset.prod_congr rfl
        intro b _
        exact ((hS a b).unique (hPg a b)).trans (hprodg a b)
      _ = ∏ i, ∏ j, Q i j :=
        prod_groupedPolynomial g.originalIndexEquiv h.originalIndexEquiv Qg

end TotalProduct

end Langlands.RankinSelberg
