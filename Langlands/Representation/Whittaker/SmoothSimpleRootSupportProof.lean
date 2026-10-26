import Langlands.Representation.Whittaker.SmoothSimpleRootSupportStatement
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalField.Normalization.Proof

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis Matrix Topology
open scoped WithZero

universe uF uV

private def adjacentUnipotent {K : Type*} [Field K] {r : ℕ}
    (i : Fin r) (t : K) : upperUnipotent (r + 1) K :=
  ⟨⟨transvection i.castSucc i.succ t, transvection i.castSucc i.succ (-t),
      by rw [transvection_mul_transvection_same _ _ (ne_of_lt i.castSucc_lt_succ),
        add_neg_cancel, transvection_zero],
      by rw [transvection_mul_transvection_same _ _ (ne_of_lt i.castSucc_lt_succ),
        neg_add_cancel, transvection_zero]⟩,
    by
      constructor
      · intro a b hab
        change transvection i.castSucc i.succ t a b = 0
        have hab' : a ≠ b := ne_of_gt hab
        have hroot : ¬ (i.castSucc = a ∧ i.succ = b) := by
          rintro ⟨rfl, rfl⟩
          exact (not_lt_of_ge i.castSucc_lt_succ.le) hab
        simp [transvection, hab', hroot]
      · intro a
        change transvection i.castSucc i.succ t a a = 1
        simp only [transvection, Matrix.add_apply, Matrix.one_apply, ite_true,
          Matrix.single_apply]
        split_ifs with h
        · exact False.elim ((ne_of_lt i.castSucc_lt_succ) (h.1.trans h.2.symm))
        · simp⟩

private theorem adjacentUnipotent_zero {K : Type*} [Field K] {r : ℕ} (i : Fin r) :
    (adjacentUnipotent i (0 : K)).val = 1 := by
  apply Units.ext
  exact transvection_zero _ _

private theorem adjacentUnipotent_continuous {K : Type*} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] {r : ℕ} (i : Fin r) :
    Continuous (fun t : K => (adjacentUnipotent i t).val) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro a <;> apply continuous_pi <;> intro b
  · change Continuous (fun t : K => transvection i.castSucc i.succ t a b)
    simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · change Continuous (fun t : K => transvection i.castSucc i.succ (-t) a b)
    simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

private theorem adjacentUnipotent_character {K : Type*} [Field K]
    [TopologicalSpace K] (ψ : UnitaryAdditiveCharacter K) {r : ℕ}
    (i : Fin r) (t : K) :
    (standardCharacter ψ r (adjacentUnipotent i t) : ℂ) = ψ.complex t := by
  rw [standardCharacter_apply]
  congr 1
  change (∑ j : Fin r, transvection i.castSucc i.succ t j.castSucc j.succ) = t
  have hentry (j : Fin r) :
      transvection i.castSucc i.succ t j.castSucc j.succ = if j = i then t else 0 := by
    simp [transvection, Matrix.single_apply,
      ne_of_lt j.castSucc_lt_succ, eq_comm]
  simp_rw [hentry]
  simp

private theorem diagonal_adjacentUnipotent {K : Type*} [Field K] {r : ℕ}
    (a : Fin (r + 1) → Kˣ) (i : Fin r) (t : K) :
    Iwasawa.diagonalUnits a * (adjacentUnipotent i t).val =
      (adjacentUnipotent i (((a i.castSucc / a i.succ : Kˣ) : K) * t)).val *
        Iwasawa.diagonalUnits a := by
  apply Units.ext
  change diagonal (fun j => (a j : K)) * transvection i.castSucc i.succ t =
    transvection i.castSucc i.succ (((a i.castSucc / a i.succ : Kˣ) : K) * t) *
      diagonal (fun j => (a j : K))
  ext j k
  simp only [diagonal_mul, mul_diagonal, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Units.val_div_eq_div_val]
  by_cases hj : i.castSucc = j <;> by_cases hk : i.succ = k <;> by_cases hjk : j = k
    <;> simp_all [ne_of_lt i.castSucc_lt_succ, eq_comm]
  field_simp

private theorem exists_uniform_lattice {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V),
      IsSmooth π → ∀ v : V, ∃ n : ℤ,
        ∀ t ∈ T.additiveLattice n,
          ∀ κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r,
            ∀ i : Fin r, π (adjacentUnipotent i t).val (π κ v) = π κ v := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro V _ _ π hπ v
  let K := Conductor.levelOpenSubgroup F.Carrier r 0
  have hK : IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) :=
    Conductor.isCompact_levelOpenSubgroup F.Carrier r 0
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S := Set.range (fun k : K => π k.val v)
  have hS : S.Finite :=
    ((Hecke.orbitMap_locallyConstant π (hπ v)).comp_continuous
      continuous_subtype_val).range_finite
  let : Finite S := hS.to_subtype
  let s : Set F.Carrier := ⋂ i : Fin r, ⋂ w : S,
    {t | π (adjacentUnipotent i t).val w.val = w.val}
  have hs : IsOpen s := by
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro w
    exact ((Hecke.orbitMap_locallyConstant π (hπ w.val)).comp_continuous
      (adjacentUnipotent_continuous i)) {w.val}
  have hzero : (0 : F.Carrier) ∈ s := by
    simp only [s, Set.mem_iInter, Set.mem_ofPred_eq, adjacentUnipotent_zero,
      map_one, Module.End.one_apply, implies_true]
  obtain ⟨n, hn⟩ := T.exists_additiveLattice_subset (hs.mem_nhds hzero)
  refine ⟨n, fun t ht κ hκ i => ?_⟩
  have hκK : κ ∈ K := by
    change κ ∈ Conductor.levelSubgroup F.Carrier r 0
    rw [Conductor.levelSubgroup_zero]
    exact hκ
  have hw : π κ v ∈ S := ⟨⟨κ, hκK⟩, rfl⟩
  exact Set.mem_iInter.mp (Set.mem_iInter.mp (hn ht) i) ⟨π κ v, hw⟩

/-- Every actual smooth Whittaker coefficient has one bound on all adjacent
root coordinates, uniform over the integral factor. -/
theorem smoothSimpleRootSupport {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r : ℕ) :
    SmoothSimpleRootSupportStatement.{uF,uV} F T r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ π hπ ℓ f
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  obtain ⟨n, hn⟩ := exists_uniform_lattice F T r π hπ v
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  refine ⟨(T.residueCardinality : ℝ) ^ (T.additiveConductor ψ - n),
    zpow_pos (lt_trans zero_lt_one hq) _, ?_⟩
  intro a κ hκ hnonzero i
  let c : F.Carrier := ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)
  have hc : c ≠ 0 := (a i.castSucc / a i.succ).ne_zero
  have hnonzero' : ℓ.val (π (Iwasawa.diagonalUnits a * κ) v) ≠ 0 := hnonzero
  have hchar (t : F.Carrier) (ht : t ∈ T.additiveLattice n) :
      ψ.complex (c * t) = 1 := by
    have hfix := hn t ht κ hκ i
    have hact : π (adjacentUnipotent i (c * t)).val
        (π (Iwasawa.diagonalUnits a * κ) v) =
        π (Iwasawa.diagonalUnits a * κ) v := by
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc,
        ← diagonal_adjacentUnipotent a i t, mul_assoc, map_mul, Module.End.mul_apply,
        map_mul, Module.End.mul_apply, hfix, map_mul, Module.End.mul_apply]
    have heq := ℓ.property (adjacentUnipotent i (c * t))
      (π (Iwasawa.diagonalUnits a * κ) v)
    rw [hact, adjacentUnipotent_character] at heq
    exact mul_right_cancel₀ hnonzero' (heq.symm.trans (one_mul _).symm)
  have hvc : T.discreteValuation c ≠ 0 := (T.discreteValuation.ne_zero_iff).mpr hc
  have htriv : T.AdditiveTrivialAt ψ (WithZero.log (T.discreteValuation c) + n) := by
    intro x hx
    have ht : x / c ∈ T.additiveLattice n := by
      change T.discreteValuation (x / c) ≤ WithZero.exp n
      rw [map_div₀, div_le_iff₀ (zero_lt_iff.mpr hvc)]
      rw [← WithZero.exp_log hvc]
      simpa only [PadicField.TopologicalData.mem_additiveLattice,
        WithZero.exp_add, mul_comm] using hx
    apply Subtype.ext
    have hcx : c * (x / c) = x := by field_simp
    simpa [hcx] using hchar (x / c) ht
  have hle := (T.additiveTrivialAt_iff_le_conductor ψ _).mp htriv
  change T.normalizedAbs c ≤ _
  rw [T.normalizedAbs_of_ne_zero hc]
  apply (zpow_le_zpow_iff_right₀ hq).mpr
  change -(-WithZero.log (T.discreteValuation c)) ≤ T.additiveConductor ψ - n
  omega

end Langlands.Whittaker
