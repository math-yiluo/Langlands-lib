import Langlands.Representation.Classification.MoeglinWaldspurgerDatumReduced
import Langlands.Representation.Classification.MoeglinWaldspurgerLabelInduction
import Langlands.Representation.Aubert.SegmentProductClass
import Langlands.Representation.Classification.TadicSpehHeads

/-!
# The derivative of a Zelevinsky label at the top point

If every occurrence of `β` ends at most at `y`, then the Zelevinsky label of `β` has
highest left `ν^{x+y} ρ`-derivative `(j, label of β - j [y, y])`, where `j` is the number of
point occurrences `[y, y]`: the field `zmax` of `DerivativeFacts` for `LDrel`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification
open Langlands.Classification.LeftCuspidalDerivative Aubert.SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

theorem point_length (y : ℤ) : (point y).length = 1 := by simp [point, Interval.length]

theorem weight_replicate_point (j : ℕ) (y : ℤ) :
    weight (Multiset.replicate j (point y)) = j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Multiset.replicate_succ, weight_cons, ih, point_length]; omega

variable (F T) in
theorem labelClass_unique {b : Multisegment} {n : ℕ} {c c' : Label.{uF, uV} F T n}
    (h : LabelClass F T ρ x b n c) (h' : LabelClass F T ρ x b n c') : c = c' := by
  let := T.topology
  have hx := Aubert.binaryProductExactness.{uF, uV} F T
  have hl := Aubert.gradedInductionRingLaws F T hx
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  exact Aubert.LanglandsHeadDuality.isLabel_unique F T hx hl ψ h h'

/-- A segment of `realize ρ x b` is the realization of an occurrence of `b`. -/
theorem mem_realize {b : Multisegment} {Δ : T.Segment.{max uF uV, uF}}
    (h : Δ ∈ realize ρ x b) : ∃ J ∈ b, J.realize ρ x = Δ :=
  Multiset.mem_map.mp h

/-- A segment socle of a realized occurrence not beginning at `y` is left reduced for
`ν^{x+y} ρ`. -/
theorem socle_leftReduced (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (y : ℤ) (J : Interval)
    (hJ : J.beginning ≠ y)
    (π : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (J.realize ρ x).degree F.Carrier))
    (hπ : T.IsSegmentSocle (J.realize ρ x) π) :
    LeftReduced F T (cuspRep F T ρ x y) π := by
  let := T.topology
  obtain ⟨-, -, -, -, hseg⟩ := hL p F T ρ.rank (cuspRep F T ρ x y)
  refine (hseg (ρ.twist (x + (y : ℝ))) rfl (cuspRep_represents F T ρ x y) _ π).2 hπ ?_
  rw [Interval.realize_base]
  intro h
  have := Langlands.Classification.cuspidalDatum_twist_injective ρ h
  have hJy : (J.beginning : ℝ) = (y : ℝ) := by linarith
  exact hJ (by exact_mod_cast hJy)

/-- **The top point.** -/
theorem zmax_LDrel (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (β : Multisegment) (y : ℤ)
    (hβ : ∀ I ∈ β, I.ending ≤ y) {n m : ℕ} (cls : Label.{uF, uV} F T n)
    (S : Label.{uF, uV} F T m) (hcls : LabelClass F T ρ x β n cls)
    (hS : LabelClass F T ρ x (β - Multiset.replicate (β.count (point y)) (point y)) m S) :
    LDrel F T ρ x y cls (β.count (point y)) S := by
  let := T.topology
  obtain ⟨j, hj⟩ : ∃ j, j = β.count (point y) := ⟨_, rfl⟩
  rw [← hj] at hS ⊢
  obtain ⟨β', hβ'⟩ : ∃ β', β' = β - Multiset.replicate j (point y) := ⟨_, rfl⟩
  have hmS := hS.degree
  rw [← hβ'] at hS hmS
  have hle : Multiset.replicate j (point y) ≤ β :=
    Multiset.le_count_iff_replicate_le.mp (le_of_eq hj)
  have hβsplit : β = Multiset.replicate j (point y) + β' := by
    rw [hβ']; exact (add_tsub_cancel_of_le hle).symm
  have hcount' : β'.count (point y) = 0 := by
    rw [hβ', Multiset.count_sub, Multiset.count_replicate_self, hj, Nat.sub_self]
  have hβ'le : ∀ J ∈ β', J.ending ≤ y := fun J hJ =>
    hβ J (Multiset.mem_of_le (by rw [hβ']; exact tsub_le_self) hJ)
  have hnβ := hcls.degree
  -- the label datum of `β'`
  obtain ⟨D₀, hD₀, hD₀S, d₀, hd₀ms, hd₀ord, hd₀soc, -, f₀, hf₀⟩ := hS
  have hD₀d₀ : SmoothRep.IsSubrepresentation D₀ d₀.induced := ⟨SmoothRep.ofHom f₀, hf₀⟩
  -- ranks
  have hN : powerRank (pointSegment ρ x y).degree j m = n := by
    rw [powerRank_eq, pointSegment_degree, ← hnβ, ← hmS, hβsplit, weight_add,
      weight_replicate_point]
    ring
  subst hN
  -- an irreducible subrepresentation of `A^j × D₀`
  let B := pointBlock F ρ x y
  have hBirr : B.IsIrreducible := pointBlock_isIrreducible ρ x y
  have : Nontrivial B := Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible
    _ hBirr
  have : Nontrivial D₀ :=
    Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hD₀
  have := iterProd_nontrivial B j D₀ inferInstance
  obtain ⟨π, hπ, f, hf⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation
    (iterProd_hasFiniteLength B (SmoothRep.hasFiniteLength_of_isIrreducible hBirr) j
      (SmoothRep.hasFiniteLength_of_isIrreducible hD₀))
  have hπB : SmoothRep.IsSubrepresentation π (iterProd T B j D₀) := ⟨f, hf⟩
  -- `π` is a label of `β`
  obtain ⟨e⟩ := iterCons_induced ρ x y j d₀
  have hπd : SmoothRep.IsSubrepresentation π (iterCons F ρ x y j d₀).induced :=
    isSubrepresentation_of_iso (isSubrepresentation_trans hπB (iterProd_mono B j hD₀d₀)) e.symm
  have hlabel : LabelClass F T ρ x β _ (GeneralLinear.irreducibleIsoClass _ F.Carrier π hπ) := by
    refine ⟨π, hπ, rfl, iterCons F ρ x y j d₀, ?_, ?_, iterCons_hasSegmentSocles ρ x y j d₀ hd₀soc,
      hπ, SmoothRep.hom hπd.choose, hπd.choose_spec⟩
    · rw [SegmentProductDatum.multisegment, iterCons_segments, ← Multiset.coe_add,
        Multiset.coe_replicate]
      change _ + d₀.multisegment = _
      rw [hd₀ms, hβsplit, realize_add]
      congr 1
      rw [realize, Multiset.map_replicate, pointSegment_eq]
    · rw [SegmentProductDatum.IsPrecedenceOrdered, isPrecedenceOrdered_iff_list,
        iterCons_segments, IsPrecedenceOrderedList, List.pairwise_append]
      refine ⟨?_, (isPrecedenceOrdered_iff_list T _).mp hd₀ord, ?_⟩
      · refine List.pairwise_replicate.mpr (Or.inr fun h => ?_)
        exact Segment.not_isLinked_self _ h.isLinked
      · intro a ha b hb hab
        rw [List.eq_of_mem_replicate ha, pointSegment_eq] at hab
        have hb' : b ∈ d₀.multisegment := Multiset.mem_coe.mpr hb
        rw [hd₀ms] at hb'
        obtain ⟨J, hJ, rfl⟩ := mem_realize ρ x hb'
        have h1 := (realize_precedes_iff F T ρ x _ _).mp hab
        have h2 := hβ'le J hJ
        dsimp only [point] at h1
        omega
  have hcls' := labelClass_unique F T ρ x hlabel hcls
  -- reducedness of `D₀`
  obtain ⟨hsq, -, -, -, -⟩ := hL p F T ρ.rank (cuspRep F T ρ x y)
  have hblocks : ∀ i, LeftReduced F T (cuspRep F T ρ x y) (d₀.blocks i) := by
    intro i
    have hi : d₀.segments i ∈ d₀.multisegment :=
      Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [hd₀ms] at hi
    obtain ⟨J, hJ, hJi⟩ := mem_realize ρ x hi
    have hJy : J.beginning ≠ y := by
      intro hb
      have hJe := hβ'le J hJ
      have hJp : J = point y := Interval.ext hb (by have := J.nonempty; simp [point]; omega)
      rw [hJp] at hJ
      exact (Multiset.count_eq_zero.mp hcount') hJ
    have key : ∀ (Δ : T.Segment.{max uF uV, uF}) (hΔ : J.realize ρ x = Δ)
        (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
        T.IsSegmentSocle Δ π → LeftReduced F T (cuspRep F T ρ x y) π := by
      intro Δ hΔ π hπ
      subst hΔ
      exact socle_leftReduced ρ x hL y J hJy π hπ
    exact key _ hJi _ (hd₀soc i)
  have hfin : ∀ i, (d₀.blocks i).HasFiniteLength := fun i =>
    SmoothRep.hasFiniteLength_of_isIrreducible
      (Aubert.SegmentProductClass.isIrreducible_of_isSegmentSocle F T (hd₀soc i))
  obtain ⟨hYred, hYfin⟩ := datum_leftReduced hL ρ.rank_pos (cuspRep F T ρ x y) _ d₀ rfl
    hblocks hfin
  have hD₀red : LeftReduced F T (cuspRep F T ρ x y) D₀ :=
    hsq m d₀.induced D₀ hYfin (SmoothRep.IsSubrepresentation.isSubquotient hD₀d₀) hYred
  -- assemble
  have hsub : SmoothRep.IsSubrepresentation π
      (T.castRank (by rw [pointSegment_degree])
        (powerProduct F T (cuspRep F T ρ x y) j D₀)) := by
    have := iterProd_castRank (pointSegment_degree ρ x y) (cuspRep F T ρ x y).obj j D₀
    have h2 : SmoothRep.IsSubrepresentation π (iterProd T
        (T.castRank (pointSegment_degree ρ x y).symm (cuspRep F T ρ x y).obj) j D₀) := hπB
    rw [powerProduct_eq_iterProd]
    rw [this] at h2
    exact h2
  rw [← hcls']
  exact ⟨_, π, hπ, D₀, hD₀, rfl, hD₀S, hD₀red, hsub⟩

end Langlands.MoeglinWaldspurger.Derivation
