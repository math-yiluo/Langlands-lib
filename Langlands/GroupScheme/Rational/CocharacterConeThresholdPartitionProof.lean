import Langlands.GroupScheme.Rational.CocharacterConeThresholdPartitionStatement
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

/-! # Proof of the cocharacter cone threshold partition -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Langlands.GroupScheme.CocharacterCone

private def thresholdCoordinates {Δ : Type u} [Fintype Δ] [DecidableEq Δ] (Q : Type v)
    (n : ℕ) :
    (Σ J : Finset Δ, Q × (↥J → Fin (n + 1)) × ({α : Δ // α ∉ J} → ℕ)) ≃
      Q × (Δ → ℕ) := by
  let coords (p : Σ J : Finset Δ, Q × (↥J → Fin (n + 1)) × ({α : Δ // α ∉ J} → ℕ))
      (α : Δ) : ℕ :=
    if h : α ∈ p.1 then p.2.2.1 ⟨α, h⟩ else n + 1 + p.2.2.2 ⟨α, h⟩
  have hmem (p) (α : Δ) : α ∈ p.1 ↔ coords p α ≤ n := by
    by_cases h : α ∈ p.1
    · refine ⟨fun _ => ?_, fun _ => h⟩
      simp only [coords, dite_eq_left h]
      exact Nat.le_of_lt_succ (p.2.2.1 ⟨α, h⟩).isLt
    · refine ⟨fun ha => (h ha).elim, fun hb => ?_⟩
      simp only [coords, dite_eq_right h] at hb
      omega
  refine Equiv.ofBijective (fun p => (p.2.1, coords p)) ⟨?_, ?_⟩
  · rintro ⟨J, r, b, t⟩ ⟨J', r', b', t'⟩ h
    have hc : coords ⟨J, r, b, t⟩ = coords ⟨J', r', b', t'⟩ := congrArg Prod.snd h
    have hr : r = r' := congrArg (Prod.fst : Q × (Δ → ℕ) → Q) h
    have hJ : J = J' := by
      apply Finset.ext
      intro α
      have hleft := hmem ⟨J, r, b, t⟩ α
      rw [congrFun hc α] at hleft
      exact hleft.trans (hmem ⟨J', r', b', t'⟩ α).symm
    subst J'
    apply congrArg (Sigma.mk J)
    refine Prod.ext hr (Prod.ext ?_ ?_)
    · funext α
      apply Fin.ext
      simpa only [coords, dite_eq_left α.property] using congrFun hc α.val
    · funext α
      apply Nat.add_left_cancel (n := n + 1)
      simpa only [coords, dite_eq_right α.property] using congrFun hc α.val
  · rintro ⟨r, m⟩
    let J := Finset.univ.filter (fun α => m α ≤ n)
    have hJ (α : Δ) : α ∈ J ↔ m α ≤ n := by simp [J]
    refine ⟨⟨J, r, fun α => ⟨m α, Nat.lt_succ_of_le ((hJ α).mp α.property)⟩,
      fun α => m α - (n + 1)⟩, Prod.ext rfl ?_⟩
    funext α
    by_cases ha : α ∈ J
    · simp only [coords, dite_eq_left ha]
    · have ht : n < m α := Nat.lt_of_not_ge (fun h => ha ((hJ α).mpr h))
      simp only [coords, dite_eq_right ha]
      omega

/-- The residue classes and bounded and strict coordinates give the stated
partition of the actual integral nonnegative quotient. -/
theorem thresholdPartition : ThresholdPartitionStatement.{u} := by
  intro k _ T R _ _ ray hpos hzero
  let A := RealTorusSpace.rootAnnihilatorInt T R
  let d (α : R) := latticePairing T α.val (ray α)
  let residues : Set (cocharacterLattice T ⧸ A) := A.mkQ '' {c | ∀ α : R,
    0 ≤ latticePairing T α.val c ∧ latticePairing T α.val c < d α}
  let pair : cocharacterLattice T →ₗ[ℤ] (R → ℤ) :=
    LinearMap.pi fun α => latticePairing T α.val
  have hker : A = pair.ker := by
    ext c
    simp only [A, RealTorusSpace.mem_rootAnnihilatorInt, LinearMap.mem_ker,
      funext_iff, pair, LinearMap.pi_apply, Pi.zero_apply]
    exact ⟨fun h α => h α.val α.property, fun h α ha => h ⟨α, ha⟩⟩
  let qeval := A.liftQ pair hker.le
  have hqeval : Function.Injective qeval :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ pair hker)
  have hResidue {r : cocharacterLattice T ⧸ A} (hr : r ∈ residues) (α : R) :
      0 ≤ qeval r α ∧ qeval r α < d α := by
    obtain ⟨c, hc, rfl⟩ := hr
    exact hc α
  have hCone {s : cocharacterLattice T ⧸ A} :
      s ∈ quotient T R ↔ ∀ α, 0 ≤ qeval s α := by
    obtain ⟨c, rfl⟩ := A.mkQ_surjective s
    rw [mkQ_mem_quotient_iff]
    exact ⟨fun h α => h α.val α.property, fun h α ha => h ⟨α, ha⟩⟩
  refine ⟨Set.Finite.of_finite_image ?_ hqeval.injOn, ?_⟩
  · refine (Set.Finite.pi (t := fun α : R => Set.Ico (0 : ℤ) (d α))
      fun _ => Set.finite_Ico _ _).subset ?_
    rintro _ ⟨p, hp, rfl⟩ α _
    exact hResidue hp α
  let raySum (m : R → ℕ) := A.mkQ (∑ β, m β • ray β)
  have hsum (m : R → ℕ) (α : R) : qeval (raySum m) α = (m α : ℤ) * d α := by
    change latticePairing T α.val (∑ β, m β • ray β) = _
    simp only [map_sum, map_nsmul, nsmul_eq_mul]
    apply Finset.sum_eq_single α
    · intro β _ hβα
      rw [hzero β α hβα.symm, mul_zero]
    · simp
  have hcoords (r : cocharacterLattice T ⧸ A) (m : R → ℕ) (α : R) :
      qeval (r + raySum m) α = qeval r α + (m α : ℤ) * d α := by
    rw [map_add, Pi.add_apply, hsum]
  let toCone (p : residues × (R → ℕ)) : quotient T R :=
    ⟨p.1.val + raySum p.2, hCone.mpr fun α => by
      rw [hcoords]
      exact add_nonneg (hResidue p.1.property α).1
        (mul_nonneg (Int.natCast_nonneg _) (hpos α).le)⟩
  have hbij : Function.Bijective toCone := by
    constructor
    · intro p p' h
      have heval (α : R) :
          qeval p.1.val α + (p.2 α : ℤ) * d α =
            qeval p'.1.val α + (p'.2 α : ℤ) * d α := by
        simpa only [toCone, hcoords] using congrArg (fun s : quotient T R => qeval s.val α) h
      have hnat : p.2 = p'.2 := by
        funext α
        have hdiv (r : residues) (m : ℕ) :
            (qeval r.val α + (m : ℤ) * d α) / d α = m := by
          rw [Int.add_mul_ediv_right _ _ (hpos α).ne', Int.ediv_eq_zero_of_lt
            (hResidue r.property α).1 (hResidue r.property α).2, zero_add]
        have heq := congrArg (fun z : ℤ => z / d α) (heval α)
        rw [hdiv, hdiv] at heq
        exact_mod_cast heq
      refine Prod.ext (Subtype.ext (hqeval (funext fun α => ?_))) hnat
      have hα := heval α
      rw [hnat] at hα
      exact add_right_cancel hα
    · intro s
      obtain ⟨x, hx⟩ := A.mkQ_surjective s.val
      have hxnonneg (α : R) : 0 ≤ latticePairing T α.val x := by
        have hxEval := (hCone.mp s.property) α
        rw [← hx] at hxEval
        exact hxEval
      let m (α : R) : ℕ := (latticePairing T α.val x / d α).toNat
      have hm (α : R) : (m α : ℤ) = latticePairing T α.val x / d α :=
        Int.natCast_toNat_eq_self.mpr (Int.ediv_nonneg (hxnonneg α) (hpos α).le)
      let y := x - ∑ β, m β • ray β
      have hy (α : R) : latticePairing T α.val y = latticePairing T α.val x % d α := by
        change latticePairing T α.val (x - _) = _
        rw [map_sub, show latticePairing T α.val (∑ β, m β • ray β) =
          (m α : ℤ) * d α from hsum m α, hm]
        exact sub_eq_iff_eq_add.mpr (Int.emod_add_ediv_mul _ _).symm
      have hres : A.mkQ y ∈ residues := ⟨y, fun α => by
        rw [hy]
        exact ⟨Int.emod_nonneg _ (hpos α).ne', Int.emod_lt_of_pos _ (hpos α)⟩, rfl⟩
      refine ⟨(⟨A.mkQ y, hres⟩, m), Subtype.ext ?_⟩
      change A.mkQ y + A.mkQ (∑ β, m β • ray β) = s.val
      rw [← map_add, sub_add_cancel, hx]
  intro n
  exact ⟨(thresholdCoordinates residues n).trans (Equiv.ofBijective toCone hbij), fun _ => rfl⟩

end Langlands.GroupScheme.CocharacterCone
