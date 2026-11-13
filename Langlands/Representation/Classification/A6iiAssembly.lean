import Langlands.Representation.Classification.A6iiGeometricSide
import Langlands.Representation.Classification.TadicExhaustionLemmasStatement
import Langlands.Representation.Classification.OrderedMultisegmentHeadExistenceProof
import Langlands.Representation.Classification.HeadTargetTransport
import Langlands.Representation.Classification.ChosenUnitaryNormalizationProof
import Langlands.Representation.Parabolic.WholeLeviConjugacyProof
import Langlands.Representation.Derivative.ProductDerivativesFiniteLength
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof

/-!
# Composition factors of the two standard modules

The normalized product of the standard modules of the factors and the standard
module of the merged segment datum have finite length and the same composition
factors; normalized products in rank zero are all equivalent.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData

universe uF uV

section JordanHolder

variable {G : Type*} [Group G]

/-- Equivalent representations of finite length have the same composition factors. -/
theorem haveSame_of_equiv {A : Rep.{uF} ℂ G} {B : Rep.{uV} ℂ G} (φ : A.ρ.Equiv B.ρ)
    (h : IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule) : HaveSameJordanHolderFactors A B := by
  obtain ⟨c, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  exact FactorMatchingProof.haveSameJordanHolderFactors_of_equiv φ
    ⟨_, LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries (A := A) c h₀ h₁⟩

end JordanHolder

variable {p : ℕ} [Fact p.Prime]

section Merged

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem merged_length_eq {n : ℕ} (c : T.SegmentProductDatum.{max uF uV, uF} n)
    {ex : Fin c.length → ℝ} (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex) :
    c.length = (merged c m).length := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (mergedEquiv c m).symm

/-- The permutation of the segments of `c` into merged order. -/
def mergedPerm {n : ℕ} (c : T.SegmentProductDatum.{max uF uV, uF} n)
    {ex : Fin c.length → ℝ} (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex) :
    Equiv.Perm (Fin c.length) :=
  (finCongr (merged_length_eq c m)).trans (mergedEquiv c m)

end Merged

/-- Irreducible and admissible blocks of a datum of segment heads. -/
theorem blocks_irreducible_admissible (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (c : T.SegmentProductDatum.{max uF uV, uF} n) (hh : c.HasSegmentHeads) :
    letI := T.topology
    (∀ l, (c.blocks l).IsIrreducible) ∧ ∀ l, (c.blocks l).IsAdmissible := by
  let := T.topology
  have hirr : ∀ l, (c.blocks l).IsIrreducible := fun l => (hh l).choose_spec.2.1
  exact ⟨hirr, fun l =>
    (CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T _ (c.blocks l) (hirr l)).1⟩

set_option maxHeartbeats 1000000 in
/-- The product of the standard modules of the factors has finite length and the
composition factors of the concatenated standard module. -/
theorem jh_concat (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (d' : ∀ i, T.SegmentProductDatum.{max uF uV, uF} (B.size i))
    (hh : ∀ i, (d' i).HasSegmentHeads) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor B).obj (fun i => (d' i).induced)).HasFiniteLength ∧
      HaveSameJordanHolderFactors
        ((T.normalizedProductInductionFunctor B).obj (fun i => (d' i).induced)).obj
        (SegmentProductDatum.concatenate B d').induced.obj := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨hirr, hadm⟩ := blocks_irreducible_admissible F T _
    (concatenate_hasSegmentHeads B d' hh)
  have hc := Parabolic.WholeLeviConjugacyProof.productInduced_finiteLength F T
    (SegmentProductDatum.concatenate B d').shape (SegmentProductDatum.concatenate B d').blocks
    hirr hadm
  let E1 := SegmentProductDatum.concatenateInducedEquiv B d'
  have hXfin : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (T.normalizedProductInduced B (fun k => (d' k).induced.representation)).asModule :=
    Derivative.ProductDerivativesFiniteLength.isFiniteLength_of_equiv E1.symm hc
  exact ⟨hXfin, haveSame_of_equiv E1 hXfin⟩

/-- Reordering the segments of `c` into merged order gives the block list of the
merged datum. -/
theorem permute_blockList_eq {F : PadicField.{uF} p} {T : F.TopologicalData} {n : ℕ}
    (c : T.SegmentProductDatum.{max uF uV, uF} n)
    {ex : Fin c.length → ℝ} (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex) :
    (c.permute (mergedPerm c m)).blockList = (merged c m).blockList := by
  have hl := merged_length_eq c m
  apply List.ext_getElem
  · simp only [SegmentProductDatum.blockList, List.length_ofFn]
    exact hl
  · intro j h1 h2
    rw [SegmentProductDatum.blockList_getElem, SegmentProductDatum.blockList_getElem]
    rfl

set_option maxHeartbeats 400000 in
/-- The standard module of a datum of segment heads has finite length. -/
theorem induced_hasFiniteLength (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV, uF} n) (hh : d.HasSegmentHeads) :
    letI := T.topology
    d.induced.HasFiniteLength := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨hirr, hadm⟩ := blocks_irreducible_admissible F T d hh
  exact Parabolic.WholeLeviConjugacyProof.productInduced_finiteLength F T d.shape d.blocks
    hirr hadm

set_option maxHeartbeats 400000 in
/-- Reordering the segments of a datum of segment heads keeps the composition
factors of its standard module. -/
theorem permute_haveSame (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{max uF uV, uF} n) (hh : d.HasSegmentHeads)
    (σ : Equiv.Perm (Fin d.length)) :
    letI := T.topology
    HaveSameJordanHolderFactors d.induced.obj (d.permute σ).induced.obj := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨hirr, hadm⟩ := blocks_irreducible_admissible F T d hh
  exact Parabolic.WholeLeviConjugacyProof.permutedProducts F T hn d.shape σ d.blocks hirr hadm

set_option maxHeartbeats 400000 in
/-- Data with equal block lists have the same standard module. -/
theorem blockList_haveSame (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (d d' : T.SegmentProductDatum.{max uF uV, uF} n) (h : d.blockList = d'.blockList)
    (hh : d.HasSegmentHeads) :
    letI := T.topology
    HaveSameJordanHolderFactors d.induced.obj d'.induced.obj := by
  let := T.topology
  obtain rfl := SegmentProductDatum.blockList_injective h
  have hfin : d.induced.HasFiniteLength := induced_hasFiniteLength F T d hh
  exact haveSame_of_equiv (A := d.induced.obj) (B := d.induced.obj)
    (Representation.Equiv.refl _) hfin

set_option maxHeartbeats 1000000 in
/-- The product of the standard modules of the factors and the merged standard
module have finite length and the same composition factors. -/
theorem jhComparison (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (hn : 0 < n)
    (B : BlockShape n) (d' : ∀ i, T.SegmentProductDatum.{max uF uV, uF} (B.size i))
    (hh : ∀ i, (d' i).HasSegmentHeads) {ex : Fin (SegmentProductDatum.concatenate B d').length → ℝ}
    (m : MergeGrouping n
      (fun ℓ => ((SegmentProductDatum.concatenate B d').segments ℓ).degree) ex) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor B).obj (fun i => (d' i).induced)).HasFiniteLength ∧
      (merged (SegmentProductDatum.concatenate B d') m).induced.HasFiniteLength ∧
      HaveSameJordanHolderFactors
        ((T.normalizedProductInductionFunctor B).obj (fun i => (d' i).induced)).obj
        (merged (SegmentProductDatum.concatenate B d') m).induced.obj := by
  let := T.topology
  have hhc := concatenate_hasSegmentHeads B d' hh
  obtain ⟨hX, H1⟩ := jh_concat F T B d' hh
  have H2 := permute_haveSame F T hn _ hhc (mergedPerm _ m)
  have H3 := blockList_haveSame F T _ _ (permute_blockList_eq _ m) (hhc.permute _)
  exact ⟨hX, induced_hasFiniteLength F T _ (merged_hasSegmentHeads _ m hhc),
    haveSameJordanHolderFactors_trans _ _ _ _ _
      (haveSameJordanHolderFactors_trans _ _ _ _ _ H1 H2) H3⟩

/-- Rank-zero normalized products are equivalent. -/
def rankZeroEquiv (F : PadicField.{uF} p) (T : F.TopologicalData) (B B' : BlockShape 0)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {V' : Fin B'.length → Type uV} [∀ i, AddCommGroup (V' i)] [∀ i, Module ℂ (V' i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (σ' : ∀ i, Representation ℂ (GeneralLinear (B'.size i) F.Carrier) (V' i)) :
    (T.normalizedProductInduced B σ).Equiv (T.normalizedProductInduced B' σ') :=
  letI := T.topology
  Representation.Equiv.mk
    ((rankZeroNormalizedProductLinearEquiv F T B σ).trans
      (rankZeroNormalizedProductLinearEquiv F T B' σ').symm)
    (fun g => by
      rw [Subsingleton.elim g 1, map_one, map_one]
      rfl)

end Langlands.Classification.A6ii
