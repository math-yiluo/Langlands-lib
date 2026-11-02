import Langlands.Representation.Classification.SegmentHeadJacquetStatement
import Langlands.Representation.Classification.SegmentSocleJacquetReduction

/-! Conditional reduction of Zelevinsky 1980, Proposition 9.5, for segment heads. -/

noncomputable section

namespace Langlands.Classification.SegmentHeadJacquetReduction

-- Reuse the identical generic helpers from the socle reduction.
open Langlands.Classification.SegmentSocleJacquetReduction (
  size_eq_of_levisAssociated_uniform refinement_size_eq eq_length_mul_of_size_eq
  eq_uniform_of_size_eq blockShape_eq_of_size_eq refinement_eq_of_size_eq
  exists_injective_surjective_of_pullback compMap compMap_apply
  exists_lift_of_mem_range exists_mem_range_of_isIrreducibleSocle flattenedRefinedJacquet
  flattenedRefinedJacquetMap flattenedRefinedJacquetMap_injective flattenedRefinedJacquetMap_surjective
  flattenedQuotient flattenedQuotient_surjective exists_refinement_size_eq
  uniformRefinement twistIsoOfEq segmentFactorTwistIso
  nonempty_productInduced_iso_uniform twistRep terminal_isRepresentedBy_twistRep
  jacquet_map_injective nontrivial_of_isIrreducible)

open GeneralLinear Geometric CuspidalSupport CategoryTheory

universe uF uV

section HeadUniqueness

universe uG uX uY uZ

variable {G : Type uG} [Group G] {V : Type uX} {W : Type uY} {W' : Type uZ}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- Two surjective intertwiners from the same representation with the same kernel have
equivalent targets. -/
theorem nonempty_equiv_of_ker_eq {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    {π' : Representation ℂ G W'} (q : ρ.IntertwiningMap π) (hq : Function.Surjective q)
    (q' : ρ.IntertwiningMap π') (hq' : Function.Surjective q')
    (h : q.toLinearMap.ker = q'.toLinearMap.ker) : Nonempty (π.Equiv π') := by
  let e : W ≃ₗ[ℂ] W' := (q.toLinearMap.quotKerEquivOfSurjective hq).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ h ≪≫ₗ q'.toLinearMap.quotKerEquivOfSurjective hq'
  have he : ∀ v, e (q v) = q' v := by
    intro v
    have h1 : (q.toLinearMap.quotKerEquivOfSurjective hq).symm (q v) =
        Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change q'.toLinearMap.quotKerEquivOfSurjective hq'
      (Submodule.quotEquivOfEq _ _ h
        ((q.toLinearMap.quotKerEquivOfSurjective hq).symm (q v))) = q' v
    rw [h1]
    rfl
  refine ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_⟩
  obtain ⟨v, rfl⟩ := hq x
  change e (π g (q v)) = π' g (e (q v))
  rw [← q.isIntertwining, he, he, q'.isIntertwining]

end HeadUniqueness

section Segment

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- Two segment heads of the same segment are isomorphic. -/
theorem nonempty_iso_of_isSegmentHead (Δ : Segment.{uV, uF} T)
    (π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (h : T.IsSegmentHead Δ π) (h' : T.IsSegmentHead Δ π') :
    Nonempty (π ≅ π') := by
  let := T.topology
  obtain ⟨A, hA, -, q, hq, huniq⟩ := h
  obtain ⟨hirr', q', hq', -⟩ := (T.isSegmentHead_iff Δ π' A hA).mp h'
  obtain ⟨e⟩ := nonempty_equiv_of_ker_eq q hq q' hq' (huniq _ π'.representation hirr' q' hq').symm
  exact ⟨SmoothRep.mkIso e⟩

/-- The decreasing segment induction is normalized parabolic induction of the external
tensor product of its block factors. -/
theorem segmentInducedDown_eq {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    T.segmentInducedDown A m hr =
      (T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj
        (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A m hr)) :=
  rfl

/-- The external tensor product of the decreasing block factors of a segment is
quasicuspidal. -/
theorem segmentFactorsDown_isLeviQuasicuspidal {r : ℕ} (m : ℕ) (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    IsLeviQuasicuspidal (BlockShape.uniform m r hr)
      (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)).representation :=
  (Classification.segmentFactorsDown_isIrreducible_isLeviCuspidal F T m hm hr A).2.2

/-- **Clause 1 of Ze80 9.5.** For an irreducible subrepresentation `π` of the decreasing
segment induction, the normalized Jacquet module along `(n - l, l)` vanishes unless the
cuspidal rank divides `l`. -/
theorem jacquet_ofPair_subsingleton
    (hH2 : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n) :
    letI := T.topology
    ∀ (Δ : Segment.{uV, uF} T)
      (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
      (j : π.representation.IntertwiningMap
        (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation),
      Function.Injective j →
      ∀ (l : ℕ) (hl : 0 < l) (hln : l < Δ.degree), ¬ Δ.rank ∣ l →
        Subsingleton ((T.normalizedJacquetFunctor
          (BlockShape.ofPair (Δ.degree - l) l (Nat.sub_pos_of_lt hln) hl
            (Nat.sub_add_cancel hln.le))).obj π) := by
  let := T.topology
  intro Δ A π j hj l hl hln hdvd
  let C := BlockShape.ofPair (Δ.degree - l) l (Nat.sub_pos_of_lt hln) hl
    (Nat.sub_add_cancel hln.le)
  rw [← not_nontrivial_iff_subsingleton]
  intro hJ
  obtain ⟨S, hS, -⟩ := exists_refinement_size_eq T Δ.rank_pos (hH2 _)
    (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos))
    (segmentFactorsDown_isLeviQuasicuspidal T Δ.length Δ.length_pos Δ.rank_pos A)
    π (SmoothRep.ofHom j) hj C _ _ (𝟙 _) (𝟙 _) (fun _ _ h => h) (fun x => ⟨x, rfl⟩) hJ
  apply hdvd
  let i₁ : Fin C.length := (1 : Fin 2)
  have h1 : l = (S i₁).length * Δ.rank :=
    eq_length_mul_of_size_eq (S i₁) (refinement_size_eq S hS i₁)
  exact ⟨(S i₁).length, h1.trans (Nat.mul_comm _ _)⟩

end Segment

section Stages

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- **Induction in stages for a decreasing segment.** The decreasing segment induction of
length `m` is the normalized induction, from the split `((m - q) r, q r)`, of the
decreasing segment inductions of the terminal piece from `ν^q A` and of the initial
piece from `A`. -/
theorem nonempty_segmentInducedDown_iso_split (Δ : Segment.{uV, uF} T) (q : ℕ)
    (hq : 0 < q) (hqm : q < Δ.length)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear Δ.rank F.Carrier)) :
    letI := T.topology
    Nonempty (T.segmentInducedDown A Δ.length Δ.rank_pos ≅
      (T.normalizedProductInductionFunctor (Δ.splitShape q hq hqm)).obj
        (Δ.splitFactors q hq hqm
          (T.segmentInducedDown (T.segmentFactor A (q : ℝ)) (Δ.length - q) Δ.rank_pos)
          (T.segmentInducedDown A q Δ.rank_pos))) := by
  let := T.topology
  let r := Δ.rank
  have hr : 0 < r := Δ.rank_pos
  let C := Δ.splitShape q hq hqm
  let len : Fin C.length → ℕ := ![Δ.length - q, q]
  have hlen : ∀ j, C.size j = len j * r := by
    intro j
    change Fin 2 at j
    fin_cases j <;> rfl
  let S : BlockRefinement C := uniformRefinement hr C len hlen
  let B := C.flatten S
  let e := C.flattenBlockEquiv S
  let h (a : (j : Fin C.length) × Fin (S j).length) : (S a.1).size a.2 = B.size (e a) :=
    (C.flatten_size_flattenBlockEquiv S a).symm
  let σ : ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size k) F.Carrier) :=
    fun k => T.segmentFactor A ((Δ.length - 1 - (k : ℕ) : ℕ) : ℝ)
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF, uV} F T Δ.degree B C S e h
    (fun j k x => C.index_index_eq_flatten S ⟨j, k⟩ x) σ
  have hB : B = BlockShape.uniform Δ.length r hr := eq_uniform_of_size_eq hr B (fun _ => rfl)
  obtain ⟨eflat⟩ := nonempty_productInduced_iso_uniform T hr B hB σ
    (T.segmentFactorsDown A Δ.length hr)
    (fun i j hij x hx => ⟨eqToIso (eq_of_heq hx) ≪≫
      eqToIso (congrArg (fun t : ℕ => T.segmentFactor A ((Δ.length - 1 - t : ℕ) : ℝ)) hij)⟩)
  let i₀ : Fin C.length := (0 : Fin 2)
  let i₁ : Fin C.length := (1 : Fin 2)
  have he₀ : ∀ k : Fin (S i₀).length, ((e ⟨i₀, k⟩ : Fin B.length) : ℕ) = k := by
    intro k
    refine (finSigmaFinEquiv_apply (n := fun j => (S j).length) ⟨i₀, k⟩).trans ?_
    exact (congrArg (· + (k : ℕ)) (Fin.sum_univ_zero _)).trans (Nat.zero_add _)
  have he₁ : ∀ k : Fin (S i₁).length,
      ((e ⟨i₁, k⟩ : Fin B.length) : ℕ) = (Δ.length - q) + k := by
    intro k
    refine (finSigmaFinEquiv_apply (n := fun j => (S j).length) ⟨i₁, k⟩).trans ?_
    exact congrArg (· + (k : ℕ)) (Fin.sum_univ_one _)
  refine ⟨eflat.symm ≪≫ ereg ≪≫ (T.normalizedProductInductionFunctor C).mapIso
    (Pi.isoMk (Fin.cons ?_ (Fin.cons ?_ finZeroElim)))⟩
  · refine (nonempty_productInduced_iso_uniform T (k := Δ.length - q) hr (S i₀) rfl _
      (T.segmentFactorsDown (T.segmentFactor A (q : ℝ)) (Δ.length - q) hr)
      fun i j hij x hx => ?_).some
    have hx' : HEq x (σ (e ⟨i₀, i⟩)) := by
      refine hx.trans ?_
      simp only [eqRec_heq_iff, heq_eq_eq]
      rfl
    have hj : (j : ℕ) < Δ.length - q := j.isLt
    have hidx : Δ.length - 1 - ((e ⟨i₀, i⟩ : Fin B.length) : ℕ) =
        (Δ.length - q - 1 - (j : ℕ)) + q := by
      rw [he₀, hij]
      omega
    exact ⟨eqToIso (eq_of_heq hx') ≪≫ (segmentFactorTwistIso T A
      ((Δ.length - q - 1 - (j : ℕ) : ℕ) : ℝ) (q : ℝ)
      ((Δ.length - 1 - ((e ⟨i₀, i⟩ : Fin B.length) : ℕ) : ℕ) : ℝ)
      (by rw [hidx, Nat.cast_add])).symm⟩
  · refine (nonempty_productInduced_iso_uniform T (k := q) hr (S i₁) rfl _
      (T.segmentFactorsDown A q hr) fun i j hij x hx => ?_).some
    have hx' : HEq x (σ (e ⟨i₁, i⟩)) := by
      refine hx.trans ?_
      simp only [eqRec_heq_iff, heq_eq_eq]
      rfl
    have hj : (j : ℕ) < q := j.isLt
    have hidx : Δ.length - 1 - ((e ⟨i₁, i⟩ : Fin B.length) : ℕ) = q - 1 - (j : ℕ) := by
      rw [he₁, hij]
      omega
    exact ⟨eqToIso (eq_of_heq hx') ≪≫
      eqToIso (congrArg (fun t : ℕ => T.segmentFactor A (t : ℝ)) hidx)⟩

end Stages

section Embedding

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- The normalized induction, from the split `((m - q) r, q r)`, of irreducible
subrepresentations of the decreasing inductions of the terminal and initial
subsegments embeds into the decreasing segment induction of `Δ`. -/
theorem exists_split_embedding (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.terminal q hqm).degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.initial q hq).degree F.Carrier))
    (h₁ : letI := T.topology
      Classification.IsIrreducibleSocle
        (T.segmentInducedDown (twistRep T (q : ℝ) A).obj (Δ.length - q)
          Δ.rank_pos).representation π₁.representation)
    (h₂ : letI := T.topology
      Classification.IsIrreducibleSocle
        (T.segmentInducedDown A.obj q Δ.rank_pos).representation π₂.representation) :
    letI := T.topology
    ∃ J : ((T.normalizedProductInductionFunctor (Δ.splitShape q hq hqm)).obj
        (Δ.splitFactors q hq hqm π₁ π₂)).representation.IntertwiningMap
        (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation,
      Function.Injective J := by
  let := T.topology
  obtain ⟨-, j₁, hj₁, -⟩ := h₁
  obtain ⟨-, j₂, hj₂, -⟩ := h₂
  obtain ⟨J, hJ⟩ := Classification.normalizedProduct_embedding_of_factor_embeddings F T
    (Δ.splitShape q hq hqm) (Δ.splitFactors q hq hqm π₁ π₂)
    (Δ.splitFactors q hq hqm
      (T.segmentInducedDown (T.segmentFactor A.obj (q : ℝ)) (Δ.length - q) Δ.rank_pos)
      (T.segmentInducedDown A.obj q Δ.rank_pos))
    (Fin.cons j₁ (Fin.cons j₂ finZeroElim)) (Fin.cons hj₁ (Fin.cons hj₂ finZeroElim))
  obtain ⟨e⟩ := nonempty_segmentInducedDown_iso_split T Δ q hq hqm A.obj
  exact ⟨(SmoothRep.equivOfIso e.symm).toIntertwiningMap.comp J,
    (SmoothRep.equivOfIso e.symm).injective.comp hJ⟩

end Embedding

section HeadFactors

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- An irreducible subrepresentation of a decreasing segment induction is irreducible and
admissible. -/
theorem isIrreducible_isAdmissible_of_isIrreducibleSocle {r : ℕ} (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (h : letI := T.topology
      Classification.IsIrreducibleSocle (T.segmentInducedDown A.obj m hr).representation
        π.representation) :
    letI := T.topology
    π.IsIrreducible ∧ IsAdmissible π.representation := by
  let := T.topology
  obtain ⟨hirr, j, hj, -⟩ := h
  exact ⟨hirr, isAdmissible_of_injective j hj
    (Classification.segmentInductionAdmissibility F T m hr A.obj A.property.2.1).2.2.2⟩

/-- The external tensor product of irreducible admissible representations of the two
blocks of the split is irreducible. -/
theorem isIrreducible_splitTensor (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length)
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.terminal q hqm).degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.initial q hq).degree F.Carrier))
    (hi₁ : letI := T.topology; π₁.IsIrreducible)
    (ha₁ : letI := T.topology; IsAdmissible π₁.representation)
    (hi₂ : letI := T.topology; π₂.IsIrreducible)
    (ha₂ : letI := T.topology; IsAdmissible π₂.representation) :
    letI := T.topology
    (FiniteTensor.externalFunctor.obj (Δ.splitFactors q hq hqm π₁ π₂)).IsIrreducible := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (Δ.terminal q hqm).degree
  let := T.generalLinearTopologicalGroup (Δ.initial q hq).degree
  have hirr : ∀ i, ((Δ.splitFactors q hq hqm π₁ π₂) i).representation.IsIrreducible :=
    Fin.cons hi₁ (Fin.cons hi₂ finZeroElim)
  have hS : ∀ i, ∀ φ : ((Δ.splitFactors q hq hqm π₁ π₂) i).representation.IntertwiningMap
      ((Δ.splitFactors q hq hqm π₁ π₂) i).representation,
      ∃ c : ℂ, φ = c • Representation.IntertwiningMap.id _ :=
    Fin.cons (fun φ => ((admissibleSchur (W := ℂ) π₁.representation ha₁ hi₁).1 φ).exists)
      (Fin.cons (fun φ => ((admissibleSchur (W := ℂ) π₂.representation ha₂ hi₂).1 φ).exists)
        finZeroElim)
  exact FiniteTensor.isIrreducible_external _ hS

/-- **Finite length.** The decreasing segment induction has finite length. -/
theorem segmentInducedDown_finiteLength
    (hH4 : ∀ n, CuspidalInductionLengthTheorem.{uF, uV} F T n) (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    letI := T.topology
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear Δ.degree F.Carrier))
      (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation.asModule := by
  let := T.topology
  have hc := Classification.segmentFactorsDown_isIrreducible_isLeviCuspidal F T Δ.length
    Δ.length_pos Δ.rank_pos A
  exact (hH4 _ (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)
    (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos))
    hc.1 hc.2).1

/-- By Zelevinsky 1980, 9.1(*), the normalized Jacquet module of a segment quotient along
the uniform shape is irreducible. -/
theorem isIrreducible_jacquet_uniform
    (hH1 : Classification.SegmentQuotientFullJacquet.{uF, uV} F T)
    (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hA : Δ.base.IsRepresentedBy A) (hπ : T.IsSegmentQuotient Δ π) :
    letI := T.topology
    ∀ B : BlockShape (Δ.length * Δ.rank), B = BlockShape.uniform Δ.length Δ.rank Δ.rank_pos →
      ((T.normalizedJacquetFunctor B).obj π).IsIrreducible := by
  let := T.topology
  intro B hB
  subst hB
  obtain ⟨e⟩ := hH1 Δ A π hA hπ
  exact (isIrreducible_iff_of_equiv e).mpr
    (Classification.segmentFactorsDown_isIrreducible_isLeviCuspidal F T Δ.length Δ.length_pos
      Δ.rank_pos A).1

end HeadFactors

section Assembly

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- **Clause 2 of Ze80 9.5, for an embedded head.** Let `π` be a segment quotient of `Δ`
that is the irreducible socle of the decreasing segment induction. Its normalized Jacquet
module along `((m - q) r, q r)` is isomorphic to the external tensor product of
irreducible subrepresentations of the decreasing inductions of the terminal and initial
subsegments. -/
theorem nonempty_split_jacquet_iso
    (hH1 : Classification.SegmentQuotientFullJacquet.{uF, uV} F T)
    (hH2 : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hH4 : ∀ n, CuspidalInductionLengthTheorem.{uF, uV} F T n) :
    letI := T.topology
    ∀ (Δ : Segment.{uV, uF} T)
      (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)),
      Δ.base.IsRepresentedBy A →
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentQuotient Δ π →
      Classification.IsIrreducibleSocle
        (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation π.representation →
    ∀ (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length)
      (π₁ : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (Δ.terminal q hqm).degree F.Carrier))
      (π₂ : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (Δ.initial q hq).degree F.Carrier)),
      Classification.IsIrreducibleSocle
        (T.segmentInducedDown (twistRep T (q : ℝ) A).obj (Δ.length - q)
          Δ.rank_pos).representation π₁.representation →
      Classification.IsIrreducibleSocle
        (T.segmentInducedDown A.obj q Δ.rank_pos).representation π₂.representation →
      Nonempty ((T.normalizedJacquetFunctor (Δ.splitShape q hq hqm)).obj π ≅
        FiniteTensor.externalFunctor.obj (Δ.splitFactors q hq hqm π₁ π₂)) := by
  let := T.topology
  intro Δ A hA π hπ hs q hq hqm π₁ π₂ h₁ h₂
  obtain ⟨hi₁, ha₁⟩ := isIrreducible_isAdmissible_of_isIrreducibleSocle T (Δ.length - q)
    Δ.rank_pos (twistRep T (q : ℝ) A) π₁ h₁
  obtain ⟨hi₂, ha₂⟩ := isIrreducible_isAdmissible_of_isIrreducibleSocle T q Δ.rank_pos A π₂ h₂
  have hW := RegularHeadExistence.nontrivial_normalizedProductInduction T
    (Δ.splitShape q hq hqm) (Δ.splitFactors q hq hqm π₁ π₂)
    (Fin.cons (nontrivial_of_isIrreducible π₁.representation hi₁)
      (Fin.cons (nontrivial_of_isIrreducible π₂.representation hi₂) finZeroElim))
  obtain ⟨J, hJ⟩ := exists_split_embedding T Δ q hq hqm A π₁ π₂ h₁ h₂
  obtain ⟨jπ, hjπ, hmem⟩ := exists_mem_range_of_isIrreducibleSocle hs
    (segmentInducedDown_finiteLength T hH4 Δ A) hW J hJ
  obtain ⟨ψ, hψ⟩ := exists_lift_of_mem_range J hJ jπ hmem
  have hψ0 : ψ ≠ 0 := by
    intro h0
    have := nontrivial_of_isIrreducible π.representation hs.1
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    have hjx : jπ x = 0 := by
      rw [← hψ, h0]
      exact map_zero J
    exact hx (hjπ (hjx.trans (map_zero jπ).symm))
  have hτ := isIrreducible_splitTensor T Δ q hq hqm π₁ π₂ hi₁ ha₁ hi₂ ha₂
  let E := Parabolic.FirstAdjointness.equiv T (Δ.splitShape q hq hqm)
    (σ := (FiniteTensor.externalFunctor.obj (Δ.splitFactors q hq hqm π₁ π₂)).representation)
    π.isSmooth
  let φ : (T.normalizedJacquetFunctor (Δ.splitShape q hq hqm)).obj π ⟶
      FiniteTensor.externalFunctor.obj (Δ.splitFactors q hq hqm π₁ π₂) :=
    SmoothRep.ofHom (E ψ)
  have hφ0 : SmoothRep.hom φ ≠ 0 := fun h => hψ0 (E.map_eq_zero_iff.mp h)
  have hφs : Function.Surjective (SmoothRep.hom φ) := by
    have := hτ
    exact (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom φ)).resolve_right
      hφ0
  have hφi : Function.Injective (SmoothRep.hom φ) :=
    jacquet_map_injective T Δ.rank_pos (hH2 _)
      (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos))
      (segmentFactorsDown_isLeviQuasicuspidal T Δ.length Δ.length_pos Δ.rank_pos A)
      π (SmoothRep.ofHom jπ) hjπ (isIrreducible_jacquet_uniform T hH1 Δ A π hA hπ)
      (Δ.splitShape q hq hqm) _ φ hφs (nontrivial_of_isIrreducible _ hτ)
  exact ⟨SmoothRep.mkIso ((SmoothRep.hom φ).ofBijective ⟨hφi, hφs⟩)⟩

/-- **Zelevinsky 1980, Proposition 9.5**, conditional on Ze80 9.1(*) for segment
quotients, BZ77 2.13(b), the existence of special segment heads (Ze80 9.1) and finite
length of irreducible cuspidal induction. -/
theorem segmentHeadJacquetFormula_of
    (hH1 : Classification.SegmentQuotientFullJacquet.{uF, uV} F T)
    (hH2 : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hH3 : Classification.SegmentSpecialConstituentExistence.{uF, uV} F T)
    (hH4 : ∀ n, CuspidalInductionLengthTheorem.{uF, uV} F T n) :
    Classification.SegmentHeadJacquetFormula.{uF, uV} F T := by
  let := T.topology
  intro Δ π hπ
  obtain ⟨A, hA, -⟩ := id hπ
  obtain ⟨π₀, hπ₀, hs₀⟩ := hH3 Δ
  obtain ⟨e⟩ := nonempty_iso_of_isSegmentHead T Δ π₀ π hπ₀ hπ
  refine ⟨fun l hl hln hdvd => ?_, fun q hq hqm => ?_⟩
  · obtain ⟨-, j, hj, -⟩ := hs₀ A hA
    have := jacquet_ofPair_subsingleton T hH2 Δ A π₀ j hj l hl hln hdvd
    exact (SmoothRep.equivOfIso ((T.normalizedJacquetFunctor _).mapIso e.symm)).injective
      |>.subsingleton
  · obtain ⟨π₁, h₁, hs₁⟩ := hH3 (Δ.terminal q hqm)
    obtain ⟨π₂, h₂, hs₂⟩ := hH3 (Δ.initial q hq)
    obtain ⟨E⟩ := nonempty_split_jacquet_iso T hH1 hH2 hH4 Δ A hA π₀ hπ₀.isSegmentQuotient
      (hs₀ A hA) q hq hqm π₁ π₂
      (hs₁ (twistRep T (q : ℝ) A) (terminal_isRepresentedBy_twistRep T Δ q hqm A hA))
      (hs₂ A hA)
    exact ⟨π₁, π₂, h₁, h₂, ⟨(T.normalizedJacquetFunctor _).mapIso e.symm ≪≫ E⟩⟩

end Assembly

/-- The conditional reduction as a proposition: for every prime `p`, p-adic field `F` and
topology `T`, Ze80 9.1(*) for segment quotients, BZ77 2.13(b) in every rank, the existence
of special segment heads and finite length of irreducible cuspidal induction in every rank
imply `SegmentHeadJacquetFormula F T`. -/
def SegmentHeadJacquetReductionClause : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    Classification.SegmentQuotientFullJacquet.{uF, uV} F T →
    (∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n) →
    Classification.SegmentSpecialConstituentExistence.{uF, uV} F T →
    (∀ n, CuspidalInductionLengthTheorem.{uF, uV} F T n) →
    Classification.SegmentHeadJacquetFormula.{uF, uV} F T

theorem segmentHeadJacquetReductionClause_holds :
    SegmentHeadJacquetReductionClause.{uF, uV} :=
  fun _ _ _ T hH1 hH2 hH3 hH4 => segmentHeadJacquetFormula_of T hH1 hH2 hH3 hH4

end Langlands.Classification.SegmentHeadJacquetReduction
