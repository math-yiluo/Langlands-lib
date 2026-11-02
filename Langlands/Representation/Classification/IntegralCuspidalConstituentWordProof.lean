import Langlands.Representation.Classification.IntegralCuspidalConstituentWordStatement
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.CuspidalSupport.IrreducibleInductionOccurrence
import Mathlib.Data.List.Perm.Basic

/-! Actual constituent words from embedding and uniqueness of support. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- An actual constituent of an integral cuspidal product realizes a
permutation of its integer labels in its normalized upper Jacquet module. -/
theorem integralCuspidalConstituentWord :
    IntegralCuspidalConstituentWord.{uF,uV} F T := by
  let := T.topology
  intro m n hn A B C e hC π hπ hsub
  classical
  let τ : Fin B.length → CuspidalDatum.{max uF uV,uF} T :=
    fun i => ⟨B.size i, B.positive i, (C i).isoClass⟩
  have hold : T.IsCuspidalConstituent τ π :=
    ⟨B.sum_eq, C, fun _ => rfl, hπ, hsub⟩
  obtain ⟨k, ρ, hemb⟩ :=
    glSupercuspidalEmbedding.{max uF uV,uF} p F T n hn π hπ
  have heq :
      (List.ofFn ρ : Multiset (CuspidalDatum.{max uF uV,uF} T)) =
        (List.ofFn τ : Multiset (CuspidalDatum.{max uF uV,uF} T)) :=
    glSupercuspidalSupportUniqueness.{max uF uV,uF} p F T n hn π hπ _ _
      ⟨k, ρ, rfl, hemb.isCuspidalConstituent⟩
      ⟨B.length, τ, rfl, hold⟩
  have hperm : (List.ofFn ρ).Perm (List.ofFn τ) :=
    Multiset.coe_eq_coe.mp heq
  let proj : CuspidalDatum.{max uF uV,uF} T →
      Σ d : ℕ, SupercuspidalClass.{max uF uV,uF} (F := F.Carrier) (n := d) :=
    fun d => ⟨d.rank, d.cls⟩
  let label : ℤ →
      Σ d : ℕ, SupercuspidalClass.{max uF uV,uF} (F := F.Carrier) (n := d) :=
    fun z => ⟨m, T.supercuspidalClassRealPowerTwist m (z : ℝ) A.isoClass⟩
  have hproj :
      (List.ofFn (fun j => proj (ρ j))).Perm
        (List.map label (List.ofFn e)) := by
    have hp := hperm.map proj
    have hτ : (fun i => proj (τ i)) = fun i => label (e i) := funext hC
    simpa only [List.map_ofFn, hτ, Function.comp_def] using hp
  have hrel := congrArg
    (fun R => R (List.ofFn (fun j => proj (ρ j))) (List.ofFn e))
    (List.eq_map_comp_perm label)
  obtain ⟨w, hw, hwp⟩ := hrel.mpr hproj
  have hwlen : w.length = k := by
    have h := congrArg List.length hw
    simpa only [List.length_ofFn, List.length_map] using h.symm
  let e' : Fin k → ℤ := fun i => w[i.val]'(by omega)
  have hwe : List.ofFn e' = w := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hwlen.symm
    · intro i hi hi'
      simp only [List.getElem_ofFn, e']
  have hlabel : ∀ j : Fin k, proj (ρ j) = label (e' j) := by
    have hh : List.ofFn (fun j => proj (ρ j)) =
        List.ofFn (fun j => label (e' j)) := by
      rw [hw, ← hwe, List.map_ofFn]
      rfl
    exact congrFun (List.ofFn_inj.mp hh)
  obtain ⟨hρ, D, hD, _, j, hj⟩ := hemb
  have hDi := (CuspidalSupport.glCuspidalTensor.{max uF uV,uF} p F T n hn
    (T.cuspidalShape ρ hρ) D).1
  let j' : π.representation.IntertwiningMap
      (T.normalizedParabolicInduced (T.cuspidalShape ρ hρ)
        (FiniteTensor.externalSmoothObject (fun i => (D i).obj)).representation) := j
  have hj0 : j' ≠ 0 := by
    let := hπ
    let : Nontrivial π :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        π.representation.asModule
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    apply hx
    apply hj
    change j' x = j' 0
    simp [h]
  have hquot0 := CuspidalSupport.isQuotient_normalizedJacquet_of_inductionHom
    F T (T.cuspidalShape ρ hρ) π
    (FiniteTensor.externalSmoothObject (fun i => (D i).obj)) hDi
  have hquot := hquot0 j' hj0
  refine ⟨w, ⟨T.cuspidalShape ρ hρ, D, e', hwe.symm, ?_,
    hquot.isSubquotient⟩, hwp⟩
  intro i
  have hcls : (D i).isoClass = (ρ i).cls := hD i
  change (⟨(ρ i).rank, (D i).isoClass⟩ :
      Σ d : ℕ, SupercuspidalClass.{max uF uV,uF} (F := F.Carrier) (n := d)) = _
  rw [hcls]
  exact hlabel i

end Langlands.Classification
