import Langlands.Representation.Classification.HeadTargetTransport
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle

/-! Endpoint reversal and smooth duality of supplied individual special heads. -/

noncomputable section

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification Classification.CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- The endpoint-reversed dual segment `[last(Δ)∨, base(Δ)∨]`. -/
def dual (Δ : Segment.{uV,uF} T) : Segment.{uV,uF} T where
  base := dualDatum Δ.last
  length := Δ.length
  length_pos := Δ.length_pos

@[simp]
theorem dual_length (Δ : Segment.{uV,uF} T) : Δ.dual.length = Δ.length := rfl

@[simp]
theorem dual_rank (Δ : Segment.{uV,uF} T) : Δ.dual.rank = Δ.rank := rfl

@[simp]
theorem dual_degree (Δ : Segment.{uV,uF} T) : Δ.dual.degree = Δ.degree := rfl

/-- The order of the members is reversed by duality. -/
theorem dual_member (Δ : Segment.{uV,uF} T) (i : ℕ) (hi : i < Δ.length) :
    Δ.dual.member i = dualDatum (Δ.member (Δ.length - 1 - i)) := by
  have hs : ((Δ.length - 1 - i : ℕ) : ℝ) + (i : ℝ) =
      ((Δ.length - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : i ≤ Δ.length - 1))
  simp only [member, dual, last, dualDatum_twist, CuspidalDatum.twist_twist]
  congr 1
  linarith

@[simp]
theorem dual_last (Δ : Segment.{uV,uF} T) : Δ.dual.last = dualDatum Δ.base := by
  rw [last, dual_length, dual_member Δ (Δ.length - 1) (by have := Δ.length_pos; omega)]
  simp

@[simp]
theorem dual_dual (Δ : Segment.{uV,uF} T) : Δ.dual.dual = Δ := by
  have hb : Δ.dual.dual.base = Δ.base := by
    change dualDatum Δ.dual.last = Δ.base
    rw [dual_last, dualDatum_dualDatum]
  cases Δ
  simp only [dual, Segment.mk.injEq] at hb ⊢
  exact ⟨hb, trivial⟩

/-- The dual support is the image of the original support under cuspidal duality. -/
theorem dual_support (Δ : Segment.{uV,uF} T) :
    Δ.dual.support = dualDatum '' Δ.support := by
  ext ρ
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨Δ.member (Δ.length - 1 - i), ⟨_, by have := Δ.length_pos; omega, rfl⟩, ?_⟩
    exact (dual_member Δ i hi).symm
  · rintro ⟨ρ, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨Δ.length - 1 - i, ?_, ?_⟩
    · change Δ.length - 1 - i < Δ.length
      have := Δ.length_pos
      omega
    rw [dual_member Δ _ (by have := Δ.length_pos; omega)]
    congr 2
    omega

end Segment

variable (T)

/-- Duality of the increasing induction gives a decreasing induction whose
base is the inverse last power twist of the dual of the original base. -/
theorem nonempty_contragredient_segmentInducedIso {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (hA : letI := T.topology; A.IsAdmissible) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup r
    letI := T.generalLinearTopologicalGroup (m * r)
    Nonempty ((T.segmentInduced A m hr).contragredient ≅
      T.segmentInducedDown
        (T.segmentFactor A.contragredient (-((m - 1 : ℕ) : ℝ))) m hr) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  let := T.generalLinearTopologicalGroup (m * r)
  let : ∀ n : ℕ, IsTopologicalGroup (GeneralLinear n F.Carrier) :=
    fun n => T.generalLinearTopologicalGroup n
  let B := BlockShape.uniform m r hr
  obtain ⟨e⟩ := CuspidalProductContragredient.nonempty_contragredient_productEquiv T B
    (fun i => (T.segmentFactors A m hr i).representation) (fun i =>
      (isAdmissible_twist_iff (T.determinantPowerCharacter r (i : ℝ))
        A.representation (T.isOpen_ker_determinantPowerCharacter r (i : ℝ))).mpr hA)
  let ef (i : Fin B.length) :
      (T.segmentFactors A m hr i).contragredient ≅
        T.segmentFactorsDown
          (T.segmentFactor A.contragredient (-((m - 1 : ℕ) : ℝ))) m hr i := by
    have hs : ((m - 1 - (i : ℕ) : ℕ) : ℝ) + (i : ℝ) =
        ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by have := i.isLt; change i.val < m at this; omega :
        (i : ℕ) ≤ m - 1))
    have hc :
        T.determinantPowerCharacter r (((m - 1 - (i : ℕ) : ℕ) : ℝ)) *
            T.determinantPowerCharacter r (-((m - 1 : ℕ) : ℝ)) =
          (T.determinantPowerCharacter r (i : ℝ))⁻¹ := by
      rw [← realPowerCharacter_add, ← realPowerCharacter_neg]
      congr 1
      linarith
    let e₀ := smoothContragredientTwistEquiv
      (T.determinantPowerCharacter r (i : ℝ)) A.representation
      (T.isOpen_ker_determinantPowerCharacter r (i : ℝ))
    have he :
        twist (T.determinantPowerCharacter r (i : ℝ))⁻¹
            (smoothContragredient A.representation) =
          twist (T.determinantPowerCharacter r (((m - 1 - (i : ℕ) : ℕ) : ℝ)))
            (twist (T.determinantPowerCharacter r (-((m - 1 : ℕ) : ℝ)))
              (smoothContragredient A.representation)) := by
      rw [twist_twist, hc]
    exact SmoothRep.mkIso (e₀.trans (equivOfRepresentationEq he))
  let E := (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk ef)
  exact ⟨(SmoothRep.mkIso e).trans E⟩

variable {T}

/-- Equivalence of the actual constituent preserves the segment head relation. -/
theorem IsSegmentHead.of_equiv {Δ : Segment.{uV,uF} T}
    {π π' : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π)
    (e : letI := T.topology; π.representation.Equiv π'.representation) :
    T.IsSegmentHead Δ π' := by
  obtain ⟨A, hA, hhead⟩ := hπ
  exact ⟨A, hA, hhead.of_targetEquiv e⟩

/-- The smooth dual of a supplied irreducible segment quotient is the strong
special head for the endpoint-reversed dual segment. -/
theorem IsSegmentQuotient.contragredient {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentQuotient Δ π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup Δ.degree
    T.IsSegmentHead Δ.dual π.contragredient := by
  let := T.topology
  let := T.generalLinearTopologicalGroup Δ.rank
  let := T.generalLinearTopologicalGroup Δ.degree
  obtain ⟨A, hA, hirr, q, hq⟩ := hπ
  let Av := twistedDualRep T (-((Δ.length - 1 : ℕ) : ℝ)) A
  have hAv : Δ.dual.base.IsRepresentedBy Av := by
    change Av.isoClass = dualClass (Δ.base.twist ((Δ.length - 1 : ℕ) : ℝ))
    rw [dualClass_def]
    change Av.isoClass =
      T.supercuspidalClassContragredient supercuspidalContragredient Δ.rank
        (T.supercuspidalClassRealPowerTwist Δ.rank ((Δ.length - 1 : ℕ) : ℝ) Δ.base.cls)
    rw [classContragredient_realPowerTwist]
    simpa only [CuspidalDatum.IsRepresentedBy, CuspidalDatum.twist, dualDatum_cls,
      dualDatum_rank, Segment.rank] using
      (twistedDualRep_represents (-((Δ.length - 1 : ℕ) : ℝ)) hA)
  obtain ⟨E⟩ := nonempty_contragredient_segmentInducedIso T A.obj A.property.2.1
    Δ.length Δ.rank_pos
  have hadm : π.IsAdmissible :=
    (CuspidalSupport.cuspidalEmbedding.{uF,max uF uV} F T Δ.degree π hirr).1
  have hdual : π.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff (compactOpen_cofinal F T Δ.degree)
      π hadm).mpr hirr
  obtain ⟨π₀, hπ₀, _⟩ := segmentSpecialConstituentExistence F T Δ.dual
  let qv := SmoothRep.contragredientHom (SmoothRep.ofHom q)
  let j := (SmoothRep.equivOfIso E).toIntertwiningMap.comp (SmoothRep.hom qv)
  have hj : Function.Injective j :=
    (SmoothRep.equivOfIso E).injective.comp
      (contragredientMap_injective_of_surjective q hq)
  obtain ⟨e⟩ := hπ₀.nonempty_equiv_of_down_subrepresentation Av hAv hdual j hj
  exact hπ₀.of_equiv e.symm

/-- Smooth duality preserves individual strong special heads, reversing endpoints. -/
theorem IsSegmentHead.contragredient {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup Δ.degree
    T.IsSegmentHead Δ.dual π.contragredient :=
  hπ.isSegmentQuotient.contragredient

end Langlands.PadicField.TopologicalData
