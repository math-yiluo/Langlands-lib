import Langlands.Representation.Classification.SegmentEdgeFactorHypotheses
import Langlands.Representation.Classification.SegmentTensorStabilizerProof

/-!
# The factor hypotheses for a slot family with one updated merged slot

Let `β = uniform m r` and let `γ` merge the adjacent blocks `k`, `k + 1` of `β`.
This module names the two hypotheses (H1) and (H2) of
`SegmentEdgeJacquetFiltration` on a family `Y` of factors on the blocks of `γ`.

For uniform supercuspidal block factors `σ`, let `Y₀ = slotProduct σ` be the slot
products, and let `W` be an invariant subspace of the merged slot product `Y₀ kk`
other than zero and the whole space. The module proves (H1) and (H2) for the
families obtained from `Y₀` by replacing the merged slot with `Y₀ kk / W`
(against the exchanged factors) or with `W` (against `σ`), and applies the
statement to them. For the factors `(A, νA, …, ν^(m-1) A)` of a segment of a
supercuspidal `A` it supplies the factor hypotheses and a subspace `W`. The
geometric lemma, Ze80 1.11(b) and `SegmentEdgeJacquetFiltration` are
hypotheses.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.SegmentEdge

open GeneralLinear Geometric CuspidalSupport CategoryTheory

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

variable {m r : ℕ} (hr : 0 < r) (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)

section Hypotheses

/-- Hypothesis (H1) of `SegmentEdgeJacquetFiltration` for a family `Y` on the
blocks of `γ = β.adjacentMerge k hk`: the normalized Jacquet module of `Y j` is
zero along every shape with at least two blocks other than `S j`, where
`S = β.adjacentRefinement k hk`. -/
def FamilyJacquetVanishing
    (Y : letI := T.topology
      ∀ j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length,
        SmoothRep.{0, uF, uW} ℂ
          (GeneralLinear (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier)) :
    Prop :=
  letI := T.topology
  ∀ j (D : BlockShape (((BlockShape.uniform m r hr).adjacentMerge k hk).size j)),
    1 < D.length → D ≠ (BlockShape.uniform m r hr).adjacentRefinement k hk j →
      Subsingleton ((T.normalizedJacquetFunctor D).obj (Y j))

/-- Hypothesis (H2) of `SegmentEdgeJacquetFiltration` for a family `Y` on the
blocks of `γ` and block factors `σ` of `β`: the normalized Jacquet module of
`Y j` along `S j` is equivalent to the external tensor product of the factors
`σ` of the blocks of `β` inside block `j`. -/
def FamilyJacquetEquiv
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (Y : letI := T.topology
      ∀ j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length,
        SmoothRep.{0, uF, uW} ℂ
          (GeneralLinear (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier)) :
    Prop :=
  letI := T.topology
  ∀ j, Nonempty (((T.normalizedJacquetFunctor
      ((BlockShape.uniform m r hr).adjacentRefinement k hk j)).obj (Y j)).representation.Equiv
    (FiniteTensor.externalSmoothObject (fun t =>
      σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩))).representation)

/-- `SegmentEdgeJacquetFiltration` applied to a family satisfying (H1) and (H2). -/
theorem jacquet_filtration_of_family (hE : SegmentEdgeJacquetFiltration.{uF, uV, uW} F T)
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (Y : letI := T.topology
      ∀ j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length,
        SmoothRep.{0, uF, uW} ℂ
          (GeneralLinear (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier))
    (h₁ : FamilyJacquetVanishing T hr k hk Y) (h₂ : FamilyJacquetEquiv T hr k hk σ Y) :
    letI := T.topology
    ∃ (N : ℕ) (e : Fin N ≃ {v : MinimalConjugatingPermutations (F := F.Carrier)
          (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) //
        IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
          (BlockShape.uniform m r hr) v.val.val})
      (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor
          (BlockShape.uniform m r hr)).obj ((T.normalizedProductInductionFunctor
            ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y)).representation) N),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
          (e i).val.val.val (e i).val.property
          (FiniteTensor.externalSmoothObject σ).representation)) :=
  hE m r hr k hk σ Y h₁ h₂

end Hypotheses

section UpdatedFamilies

/-- A slot of the merged shape is the merged slot exactly when its index is `k`. -/
theorem ne_adjacentMergeIndex_iff
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) :
    j ≠ (BlockShape.uniform m r hr).adjacentMergeIndex k hk ↔ j.val ≠ k := by
  rw [Ne, Fin.ext_iff, BlockShape.adjacentMergeIndex_val]

/-- (H1) for the slot products with the merged slot replaced by its quotient by
`W`, from the geometric lemma. -/
theorem updateQuotient_jacquet_subsingleton (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation)
    (W : letI := T.topology
      Subrepresentation (slotProduct T hr k hk σ
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    FamilyJacquetVanishing T hr k hk
      (Function.update (slotProduct T hr k hk σ)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
        (SmoothRep.quotient (slotProduct T hr k hk σ
          ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) := by
  let := T.topology
  intro j D hD hne
  by_cases hj : j = (BlockShape.uniform m r hr).adjacentMergeIndex k hk
  · subst hj
    rw [Function.update_self]
    exact slot_quotient_jacquet_subsingleton T hr k hk hgeo σ hσ _ W D hD hne
  · rw [Function.update_of_ne hj]
    exact slot_jacquet_subsingleton T hr k hk hgeo σ hσ j D hD hne

/-- (H1) for the slot products with the merged slot replaced by `W`, from the
geometric lemma. -/
theorem updateSubrepresentation_jacquet_subsingleton
    (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation)
    (W : letI := T.topology
      Subrepresentation (slotProduct T hr k hk σ
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    FamilyJacquetVanishing T hr k hk
      (Function.update (slotProduct T hr k hk σ)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
        (SmoothRep.subrepresentation (slotProduct T hr k hk σ
          ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) := by
  let := T.topology
  intro j D hD hne
  by_cases hj : j = (BlockShape.uniform m r hr).adjacentMergeIndex k hk
  · subst hj
    rw [Function.update_self]
    exact slot_subrepresentation_jacquet_subsingleton T hr k hk hgeo σ hσ _ W D hD hne
  · rw [Function.update_of_ne hj]
    exact slot_jacquet_subsingleton T hr k hk hgeo σ hσ j D hD hne

/-- (H2) for the slot products with the merged slot replaced by its quotient by
`W`, against the factors with blocks `k`, `k + 1` exchanged, from Ze80 1.11(b). -/
theorem updateQuotient_jacquet_equiv
    (hjac : TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T)
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hρ : letI := T.topology; σ ⟨k, by omega⟩ = ρ.obj)
    (hρ' : letI := T.topology; σ ⟨k + 1, hk⟩ = ρ'.obj)
    (hadj : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ.isoClass ∨
        ρ.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ'.isoClass)
    (W : letI := T.topology
      Subrepresentation (slotProduct T hr k hk σ
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation)
    (hW₀ : W ≠ ⊥) (hW₁ : W ≠ ⊤) :
    letI := T.topology
    FamilyJacquetEquiv T hr k hk (swappedFactors T hr k hk σ)
      (Function.update (slotProduct T hr k hk σ)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
        (SmoothRep.quotient (slotProduct T hr k hk σ
          ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) := by
  let := T.topology
  intro j
  by_cases hj : j = (BlockShape.uniform m r hr).adjacentMergeIndex k hk
  · subst hj
    rw [Function.update_self]
    exact (merged_jacquet_equiv T hr k hk hjac σ ρ ρ' hρ hρ' hadj W hW₀ hW₁).2
  · rw [Function.update_of_ne hj]
    exact slot_jacquet_equiv_swapped_of_ne T hr k hk σ j
      ((ne_adjacentMergeIndex_iff hr k hk j).mp hj)

/-- (H2) for the slot products with the merged slot replaced by `W`, against the
factors `σ`, from Ze80 1.11(b). -/
theorem updateSubrepresentation_jacquet_equiv
    (hjac : TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T)
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hρ : letI := T.topology; σ ⟨k, by omega⟩ = ρ.obj)
    (hρ' : letI := T.topology; σ ⟨k + 1, hk⟩ = ρ'.obj)
    (hadj : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ.isoClass ∨
        ρ.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ'.isoClass)
    (W : letI := T.topology
      Subrepresentation (slotProduct T hr k hk σ
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation)
    (hW₀ : W ≠ ⊥) (hW₁ : W ≠ ⊤) :
    letI := T.topology
    FamilyJacquetEquiv T hr k hk σ
      (Function.update (slotProduct T hr k hk σ)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
        (SmoothRep.subrepresentation (slotProduct T hr k hk σ
          ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) := by
  let := T.topology
  intro j
  by_cases hj : j = (BlockShape.uniform m r hr).adjacentMergeIndex k hk
  · subst hj
    rw [Function.update_self]
    exact (merged_jacquet_equiv T hr k hk hjac σ ρ ρ' hρ hρ' hadj W hW₀ hW₁).1
  · rw [Function.update_of_ne hj]
    exact slot_jacquet_equiv_of_ne T hr k hk σ j ((ne_adjacentMergeIndex_iff hr k hk j).mp hj)

end UpdatedFamilies

section Segment

/-- Every block factor `ν^i A` of a segment of a supercuspidal `A` is irreducible
and supercuspidal. -/
theorem segmentFactors_irreducible_supercuspidal
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∀ i, (T.segmentFactors A.obj m hr i).IsIrreducible ∧
      IsSupercuspidal (T.segmentFactors A.obj m hr i).representation := by
  let := T.topology
  intro i
  exact (segmentSupercuspidalFactor F T A ((i : ℕ) : ℝ)).property

/-- Block `k` of the segment factors is the supercuspidal object `ν^k A`. -/
theorem segmentFactors_eq_left
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    T.segmentFactors A.obj m hr ⟨k, by omega⟩ = (segmentSupercuspidalFactor F T A (k : ℝ)).obj :=
  rfl

/-- Block `k + 1` of the segment factors is the supercuspidal object `ν^(k+1) A`. -/
theorem segmentFactors_eq_right
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    T.segmentFactors A.obj m hr ⟨k + 1, hk⟩ =
      (segmentSupercuspidalFactor F T A ((k + 1 : ℕ) : ℝ)).obj :=
  rfl

/-- The class of `ν^s A` is the `|det|^s` twist of the class of `A`. -/
theorem segmentSupercuspidalFactor_isoClass
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) (s : ℝ) :
    letI := T.topology
    (segmentSupercuspidalFactor F T A s).isoClass =
      T.supercuspidalClassRealPowerTwist r s A.isoClass :=
  rfl

/-- The class of `ν^(k+1) A` is the twist by `ν` of the class of `ν^k A`. -/
theorem segmentSupercuspidalFactor_succ_isoClass
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) (k : ℕ) :
    letI := T.topology
    (segmentSupercuspidalFactor F T A ((k + 1 : ℕ) : ℝ)).isoClass =
      T.supercuspidalClassRealPowerTwist r 1
        (segmentSupercuspidalFactor F T A (k : ℝ)).isoClass := by
  let := T.topology
  rw [segmentSupercuspidalFactor_isoClass, segmentSupercuspidalFactor_isoClass,
    T.supercuspidalClassRealPowerTwist_add]
  congr 1
  push_cast
  ring

/-- Ze80 1.11(b), composition clause, for a segment: the merged slot product
`ν^k A × ν^(k+1) A` has an invariant subspace other than zero and the whole
space. -/
theorem segment_exists_proper_subrepresentation
    (hcomp : TwoSupercuspidalAdjacentProductComposition.{uF, uV} F T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∃ W : Subrepresentation (slotProduct T hr k hk (T.segmentFactors A.obj m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation,
      W ≠ ⊥ ∧ W ≠ ⊤ := by
  let := T.topology
  exact (merged_composition T hr k hk hcomp (T.segmentFactors A.obj m hr)
    (segmentSupercuspidalFactor F T A (k : ℝ))
    (segmentSupercuspidalFactor F T A ((k + 1 : ℕ) : ℝ))
    (segmentFactors_eq_left T hr k hk A) (segmentFactors_eq_right T hr k hk A)
    (Or.inl (segmentSupercuspidalFactor_succ_isoClass T A k))).2.1.exists

/-- (H1) and (H2), against the exchanged factors, for the segment slot products
with the merged slot replaced by its quotient by some invariant subspace. -/
theorem segment_updateQuotient_hypotheses (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (hcomp : TwoSupercuspidalAdjacentProductComposition.{uF, uV} F T)
    (hjac : TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∃ W : Subrepresentation (slotProduct T hr k hk (T.segmentFactors A.obj m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation,
      FamilyJacquetVanishing T hr k hk
          (Function.update (slotProduct T hr k hk (T.segmentFactors A.obj m hr))
            ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
            (SmoothRep.quotient (slotProduct T hr k hk (T.segmentFactors A.obj m hr)
              ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) ∧
        FamilyJacquetEquiv T hr k hk (swappedFactors T hr k hk (T.segmentFactors A.obj m hr))
          (Function.update (slotProduct T hr k hk (T.segmentFactors A.obj m hr))
            ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
            (SmoothRep.quotient (slotProduct T hr k hk (T.segmentFactors A.obj m hr)
              ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) := by
  let := T.topology
  obtain ⟨W, hW₀, hW₁⟩ := segment_exists_proper_subrepresentation T hr k hk hcomp A
  refine ⟨W, ?_, ?_⟩
  · exact updateQuotient_jacquet_subsingleton T hr k hk hgeo (T.segmentFactors A.obj m hr)
      (segmentFactors_irreducible_supercuspidal T hr A) W
  · exact updateQuotient_jacquet_equiv T hr k hk hjac (T.segmentFactors A.obj m hr)
      (segmentSupercuspidalFactor F T A (k : ℝ))
      (segmentSupercuspidalFactor F T A ((k + 1 : ℕ) : ℝ))
      (segmentFactors_eq_left T hr k hk A) (segmentFactors_eq_right T hr k hk A)
      (Or.inl (segmentSupercuspidalFactor_succ_isoClass T A k)) W hW₀ hW₁

/-- (H1) and (H2), against the segment factors, for the segment slot products
with the merged slot replaced by some invariant subspace. -/
theorem segment_updateSubrepresentation_hypotheses (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (hcomp : TwoSupercuspidalAdjacentProductComposition.{uF, uV} F T)
    (hjac : TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∃ W : Subrepresentation (slotProduct T hr k hk (T.segmentFactors A.obj m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation,
      FamilyJacquetVanishing T hr k hk
          (Function.update (slotProduct T hr k hk (T.segmentFactors A.obj m hr))
            ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
            (SmoothRep.subrepresentation (slotProduct T hr k hk (T.segmentFactors A.obj m hr)
              ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) ∧
        FamilyJacquetEquiv T hr k hk (T.segmentFactors A.obj m hr)
          (Function.update (slotProduct T hr k hk (T.segmentFactors A.obj m hr))
            ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
            (SmoothRep.subrepresentation (slotProduct T hr k hk (T.segmentFactors A.obj m hr)
              ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) := by
  let := T.topology
  obtain ⟨W, hW₀, hW₁⟩ := segment_exists_proper_subrepresentation T hr k hk hcomp A
  refine ⟨W, ?_, ?_⟩
  · exact updateSubrepresentation_jacquet_subsingleton T hr k hk hgeo (T.segmentFactors A.obj m hr)
      (segmentFactors_irreducible_supercuspidal T hr A) W
  · exact updateSubrepresentation_jacquet_equiv T hr k hk hjac (T.segmentFactors A.obj m hr)
      (segmentSupercuspidalFactor F T A (k : ℝ))
      (segmentSupercuspidalFactor F T A ((k + 1 : ℕ) : ℝ))
      (segmentFactors_eq_left T hr k hk A) (segmentFactors_eq_right T hr k hk A)
      (Or.inl (segmentSupercuspidalFactor_succ_isoClass T A k)) W hW₀ hW₁

end Segment

end Langlands.Classification.SegmentEdge
