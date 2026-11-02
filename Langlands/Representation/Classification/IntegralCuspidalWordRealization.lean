import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Group.GL.AdjacentMergeShape

/-! Recover the actual tensor attached to any given labeling of a realized word. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- An actual word retains its total rank, including all multiplicities. -/
theorem integralCuspidalJacquetWord_length_mul :
    letI := T.topology
    ∀ (m n : ℕ)
      (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (w : List ℤ),
      IntegralCuspidalJacquetWord F T m n A π w → w.length * m = n := by
  let := T.topology
  intro m n A π w ⟨B, C, e, hw, hC, _⟩
  have hsize (i : Fin B.length) : B.size i = m := congrArg Sigma.fst (hC i)
  rw [hw, List.length_ofFn]
  calc
    B.length * m = ∑ i : Fin B.length, B.size i := by simp [hsize]
    _ = n := B.sum_eq

theorem integralCuspidalJacquetWord_occurrence_of_labeling :
    letI := T.topology
    ∀ (m n : ℕ)
      (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
      (B : BlockShape n)
      (C : ∀ i : Fin B.length,
        SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i))
      (e : Fin B.length → ℤ)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      (∀ i : Fin B.length,
        (⟨B.size i, (C i).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
            ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩) →
      IntegralCuspidalJacquetWord F T m n A π (List.ofFn e) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
        ((T.normalizedJacquetFunctor B).obj π) := by
  let := T.topology
  intro m n A B C e π hC hword
  classical
  obtain ⟨B', C', e', hw, hC', hocc⟩ := hword
  have hlen : B'.length = B.length := by
    simpa only [List.length_ofFn] using (congrArg List.length hw).symm
  have hB : B' = B :=
    BlockShape.ext_of_size hlen fun i =>
      (congrArg Sigma.fst (hC' i)).trans
        (congrArg Sigma.fst (hC (Fin.cast hlen i))).symm
  cases hB
  have he : e = e' := List.ofFn_inj.mp hw
  cases he
  have hclasses (i : Fin B.length) : (C' i).isoClass = (C i).isoClass :=
    eq_of_heq (Sigma.mk.inj_iff.mp ((hC' i).trans (hC i).symm)).2
  let E : ∀ i, (C' i).obj ≅ (C i).obj := fun i =>
    (supercuspidalProperty (F := F.Carrier) (n := B.size i)).ι.mapIso
      (Classical.choice ((SupercuspidalRep.isoClass_eq_iff _ _).mp (hclasses i)))
  exact hocc.of_iso_left (FiniteTensor.externalFunctor.mapIso (Pi.isoMk E))

end Langlands.Classification
