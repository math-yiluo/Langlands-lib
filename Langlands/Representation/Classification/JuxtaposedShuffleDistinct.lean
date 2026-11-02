import Langlands.Representation.Classification.JuxtaposedShuffleInducedIso
import Langlands.Representation.Classification.SegmentTensorStabilizerProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof

/-!
# Distinct shuffles give inequivalent shuffle tensors

For the juxtaposed runs `l, …, l+q-1` and `0, …, l-1`, the shuffle tensors
`τ_S = ⊗ₖ ν^(e_S(k)) A` of two shuffle sets of size `q` are equivalent only when the
sets are equal. An equivalence of the tensors restricts, on each block subgroup, to
an equivalence of the corresponding factors; equivalent integral twists of `A` have
equal exponents; and the exponents determine the shuffle set.
-/

noncomputable section

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear PadicField.TopologicalData CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Equivalent natural twists `ν^a A` and `ν^b A` of a supercuspidal representation
have `a = b`. -/
theorem eq_of_segmentFactor_equiv {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) (a b : ℕ)
    (E : letI := T.topology
      (T.segmentFactor A.obj (a : ℝ)).representation.Equiv
        (T.segmentFactor A.obj (b : ℝ)).representation) : a = b := by
  let := T.topology
  have h := cuspidalDatum_eq_of_equiv
    (ρ₁ := ⟨r, hr, (segmentSupercuspidalFactor F T A (a : ℝ)).isoClass⟩)
    (ρ₂ := ⟨r, hr, (segmentSupercuspidalFactor F T A (b : ℝ)).isoClass⟩)
    (segmentSupercuspidalFactor F T A (a : ℝ)) (segmentSupercuspidalFactor F T A (b : ℝ))
    rfl rfl (Equiv.refl _) (MonoidHom.id _) (fun _ _ _ => rfl) E
  change (⟨r, hr, A.isoClass⟩ : CuspidalDatum.{uV, uF} T).twist (a : ℝ) =
    (⟨r, hr, A.isoClass⟩ : CuspidalDatum.{uV, uF} T).twist (b : ℝ) at h
  apply Int.ofNat_inj.mp
  apply cuspidalDatum_integralTwist_injective F T (⟨r, hr, A.isoClass⟩ : CuspidalDatum T)
  simpa only [Int.cast_natCast] using h

/-- Two shuffle sets of size `q` with equivalent shuffle tensors are equal. -/
theorem eq_of_shuffleTensor_equiv {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    {q l : ℕ} {S S' : Finset (Fin (q + l))} (hS : S.card = q) (hS' : S'.card = q)
    (E : letI := T.topology
      (FiniteTensor.externalSmoothObject
        (shuffleFactors F T A.obj (q + l) hr S l 0)).representation.Equiv
      (FiniteTensor.externalSmoothObject
        (shuffleFactors F T A.obj (q + l) hr S' l 0)).representation) :
    S = S' := by
  let := T.topology
  refine eq_of_shuffleExponent_eq hS hS' fun k => ?_
  have hirr : ∀ s : ℝ, Representation.IsIrreducible (T.segmentFactor A.obj s).representation :=
    fun s => (segmentSupercuspidalFactor F T A s).property.1
  have : ∀ s : ℝ, Nontrivial (T.segmentFactor A.obj s) := fun s =>
    nontrivial_of_isIrreducible (T.segmentFactor A.obj s).representation (hρ := hirr s)
  have hE : Nonempty ((T.segmentFactor A.obj (shuffleExponent S l 0 k)).representation.Equiv
      (T.segmentFactor A.obj (shuffleExponent S' l 0 k)).representation) := by
    refine nonempty_equiv_of_factor_actions (i₀ := k) (j₀ := k)
      (V := fun i => T.segmentFactor A.obj (shuffleExponent S l 0 i))
      (W := fun i => T.segmentFactor A.obj (shuffleExponent S' l 0 i))
      (hρ := hirr _) (hσ := hirr _) ?_ ?_
      (equivComp E (MonoidHom.mulSingle _ k))
    · intro g v
      have hl := external_mulSingle_tprod
        (fun i => (shuffleFactors F T A.obj (q + l) hr S l 0 i).representation) k g v
      exact hl
    · intro g w
      have hl := external_mulSingle_tprod
        (fun i => (shuffleFactors F T A.obj (q + l) hr S' l 0 i).representation) k g w
      exact hl
  obtain ⟨E'⟩ := hE
  obtain ⟨a, ha⟩ := exists_natCast_shuffleExponent S l k
  obtain ⟨b, hb⟩ := exists_natCast_shuffleExponent S' l k
  rw [ha, hb] at E' ⊢
  rw [eq_of_segmentFactor_equiv T hr A a b E']

end Langlands.Classification.JuxtaposedShuffle
