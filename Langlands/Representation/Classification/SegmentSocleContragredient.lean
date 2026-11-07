import Langlands.Representation.Classification.ProductConstituentContragredient

/-! Endpoint-reversed smooth duality for individual strong segment socles. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification Classification.CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

set_option maxHeartbeats 1600000 in
/-- The smooth dual of a strong segment socle is the strong socle of the
endpoint-reversed dual segment. -/
theorem IsSegmentSocle.contragredient {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup Δ.degree
    T.IsSegmentSocle Δ.dual π.contragredient := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  obtain ⟨A, hA, hs⟩ := hπ
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
  let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  have hirr (i : Fin B.length) :
      Representation.IsIrreducible (T.segmentFactors A.obj Δ.length Δ.rank_pos i).representation :=
    (isIrreducible_twist_iff _ _).mpr A.property.1
  have hdual := hs.contragredient_product T Δ.degree_pos B
    (T.segmentFactors A.obj Δ.length Δ.rank_pos) hirr
  let ef (i : Fin B.reverse.length) : Representation.Equiv
      (smoothContragredient
        (T.segmentFactors A.obj Δ.length Δ.rank_pos i.rev).representation)
      (T.segmentFactors Av.obj Δ.length Δ.rank_pos i).representation := by
    have hs : ((Δ.length - 1 - (i : ℕ) : ℕ) : ℝ) + (i : ℝ) =
        ((Δ.length - 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel
        (by have := i.isLt; change i.val < Δ.length at this; omega :
          (i : ℕ) ≤ Δ.length - 1))
    have hc :
        T.determinantPowerCharacter Δ.rank (i : ℝ) *
            T.determinantPowerCharacter Δ.rank (-((Δ.length - 1 : ℕ) : ℝ)) =
          (T.determinantPowerCharacter Δ.rank (i.rev : ℝ))⁻¹ := by
      rw [← realPowerCharacter_add, ← realPowerCharacter_neg]
      congr 1
      have hrev : (i.rev : ℕ) = Δ.length - 1 - (i : ℕ) := by
        simp only [Fin.val_rev]
        change Δ.length - ((i : ℕ) + 1) = Δ.length - 1 - (i : ℕ)
        omega
      rw [hrev]
      linarith
    let e₀ := smoothContragredientTwistEquiv
      (T.determinantPowerCharacter Δ.rank (i.rev : ℝ)) A.obj.representation
      (T.isOpen_ker_determinantPowerCharacter Δ.rank (i.rev : ℝ))
    have he :
        twist (T.determinantPowerCharacter Δ.rank (i.rev : ℝ))⁻¹
            (smoothContragredient A.obj.representation) =
          (T.segmentFactors Av.obj Δ.length Δ.rank_pos i).representation := by
      change _ = twist (T.determinantPowerCharacter Δ.rank (i : ℝ))
        (twist (T.determinantPowerCharacter Δ.rank (-((Δ.length - 1 : ℕ) : ℝ)))
          (smoothContragredient A.obj.representation))
      rw [twist_twist, hc]
    exact e₀.trans (equivOfRepresentationEq he)
  let E := T.normalizedProductInducedEquiv B.reverse ef
  exact ⟨Av, hAv, hdual.of_equiv E⟩

end Langlands.PadicField.TopologicalData
