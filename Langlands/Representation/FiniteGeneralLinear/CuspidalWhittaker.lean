import Langlands.Representation.FiniteGeneralLinear.Cuspidal
import Langlands.Representation.FiniteGeneralLinear.FiniteAdditiveWeights
import Langlands.Representation.FiniteGeneralLinear.WhittakerColumnDescent
import Langlands.Representation.Derivative.MinusVanishing
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.Whittaker.UpperUnipotentCoinvariantReduction

/-! Cuspidal representations of a finite general linear group have Whittaker vectors. -/

noncomputable section

open Langlands.GeneralLinear Langlands.Whittaker
open scoped BigOperators Matrix

namespace Langlands.FiniteGeneralLinear

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- The space of vectors transforming by the standard upper-unipotent character. -/
def whittakerVectors (ρ : Representation ℂ (GeneralLinear n k) V) (ψ : AddChar k ℂ) :
    Submodule ℂ V where
  carrier := {v | ∀ u : upperUnipotent n k, ρ u.val v = (entrywiseCharacter ψ n u : ℂ) • v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw u
    rw [map_add, smul_add, hv u, hw u]
  smul_mem' := by
    intro c v hv u
    rw [map_smul, hv u, smul_comm]

@[simp] theorem mem_whittakerVectors (ρ : Representation ℂ (GeneralLinear n k) V)
    (ψ : AddChar k ℂ) (v : V) : v ∈ whittakerVectors ρ ψ ↔
      ∀ u : upperUnipotent n k, ρ u.val v = (entrywiseCharacter ψ n u : ℂ) • v := Iff.rfl

namespace WhittakerDescent

open ProductLeviChamber (twoBlock)
open Whittaker.UpperUnipotentCoinvariant (cutShape_parabolic_ne_top isBlockUnipotent_of_mem_cutShape)
open Classification.SupercuspidalDerivativeVanishing
  (mem_upperUnipotent_of_isBlockUnipotent)

private def finalRow (m : ℕ) (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

private theorem exists_lastRow {m : ℕ} (hm : 0 < m) (a : Fin m → k) (ha : a ≠ 0) :
    ∃ g : GeneralLinear m k, (fun j => g.val (finalRow m hm) j) = a := by
  cases m with
  | zero => omega
  | succ m =>
    have h : finalRow (m + 1) hm = Fin.last m := Fin.ext (by simp [finalRow])
    rw [h]
    exact Langlands.Derivative.Mirabolic.exists_lastRow_eq_of_ne_zero a ha

private theorem column_character (ψ : AddChar k ℂ) (p : Fin (n + 1)) (hp : 0 < p.val)
    (x : Fin p.val → k) :
    (entrywiseCharacter ψ (n + 1) (column p (Multiplicative.ofAdd x)) : ℂ) =
      ψ (x (finalRow p.val hp)) := by
  let i : Fin n := ⟨p.val - 1, by have := p.isLt; omega⟩
  have hs : i.succ = p := Fin.ext (by simp [i]; omega)
  rw [entrywiseCharacter_apply_sum, Fintype.sum_eq_single i]
  · congr 1
    rw [column_entry, hs, Matrix.one_apply]
    have hi : i.castSucc.val < p.val := by
      rw [← hs]
      exact i.castSucc_lt_succ
    have hne : i.castSucc ≠ p := fun h => (Nat.lt_irrefl _) (h ▸ hi)
    rw [ite_eq_right hne, zero_add, dite_eq_left hi, ite_eq_left rfl]
    rfl
  · intro j hj
    have hne : j.succ ≠ p := fun h => hj (Fin.succ_injective _ (h.trans hs.symm))
    rw [column_entry, Matrix.one_apply, ite_eq_right (ne_of_lt j.castSucc_lt_succ)]
    simp [hne]

private theorem rho_mul {G : Type*} [Group G] (ρ : Representation ℂ G V) (g h : G) (v : V) :
    ρ (g * h) v = ρ g (ρ h v) := by rw [map_mul, Module.End.mul_apply]

private abbrev StageWeight (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (ψ : AddChar k ℂ) (m : ℕ) (v : V) : Prop :=
  ∀ u : upperUnipotent (n + 1) k, FixesColumns m u.val →
    ρ u.val v = (entrywiseCharacter ψ (n + 1) u : ℂ) • v

private theorem entrywise_eq_of_fixedColumns (ψ : AddChar k ℂ) (p : Fin (n + 1))
    {u u' : upperUnipotent (n + 1) k}
    (hu : FixesColumns (p.val + 1) u.val) (hu' : FixesColumns (p.val + 1) u'.val)
    (ht : ∀ i j : Fin (n + 1), p.val ≤ i.val → p.val ≤ j.val → u'.val.val i j = u.val.val i j) :
    (entrywiseCharacter ψ (n + 1) u' : ℂ) = (entrywiseCharacter ψ (n + 1) u : ℂ) := by
  simp only [entrywiseCharacter_apply_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p.val ≤ i.val
  · exact ht _ _ hi (by simp; omega)
  · have hj : i.succ.val < p.val + 1 := by simp; omega
    exact (hu' _ _ hj).trans (hu _ _ hj).symm

private theorem stageStep [Finite k] (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (hcusp : IsCuspidal ρ) {ψ : AddChar k ℂ} (hψ : ψ ≠ 0)
    (p : Fin (n + 1)) (hp : 0 < p.val) (v : V) (hv : v ≠ 0)
    (hv' : StageWeight ρ ψ (p.val + 1) v) :
    ∃ w : V, w ≠ 0 ∧ StageWeight ρ ψ p.val w := by
  classical
  let A := Fin p.val → k
  let : Fintype A := Fintype.ofFinite A
  let U := upperUnipotent (n + 1) k
  let θ := entrywiseCharacter ψ (n + 1)
  let σ : Representation ℂ (Multiplicative A) V := ρ.comp (U.subtype.comp (column p))
  let z (χ : AddChar A ℂ) := additiveWeightSum σ χ v
  have hnext (χ : AddChar A ℂ) : StageWeight ρ ψ (p.val + 1) (z χ) := by
    intro u hu
    change ρ u.val (∑ x : A, χ (-x) • σ (Multiplicative.ofAdd x) v) =
      (θ u : ℂ) • ∑ x : A, χ (-x) • σ (Multiplicative.ofAdd x) v
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    let c := column p (Multiplicative.ofAdd x)
    let u' := c⁻¹ * u * c
    have he : u * c = c * u' := by simp [u', ← mul_assoc]
    have hθ : θ u' = θ u := by simp [u', map_mul, mul_assoc, mul_comm]
    have hu' := fixesColumns_column_conj p hu x
    have h : ρ u.val (ρ c.val v) = (θ u : ℂ) • ρ c.val v := calc
      _ = ρ c.val (ρ u'.val v) := by
        simpa only [Subgroup.coe_mul, rho_mul] using
          congrArg (fun y : U => ρ y.val v) he
      _ = _ := by rw [hv' u' hu', hθ, map_smul]
    change ρ u.val (χ (-x) • ρ c.val v) = (θ u : ℂ) • (χ (-x) • ρ c.val v)
    rw [map_smul, h, smul_comm (χ (-x)) (θ u : ℂ)]
  have hcolumn (χ : AddChar A ℂ) (x : A) :
      ρ (column p (Multiplicative.ofAdd x)).val (z χ) = χ x • z χ :=
    apply_additiveWeightSum σ χ v x
  have hzero : z 0 = 0 := by
    apply hcusp (twoBlock (n + 1) p.val hp p.isLt)
      (cutShape_parabolic_ne_top _ _ hp p.isLt)
    intro u hu
    have hb := isBlockUnipotent_of_mem_cutShape hp p.isLt hu
    let u₀ : U := ⟨u, mem_upperUnipotent_of_isBlockUnipotent hb⟩
    have hfixed : FixesColumns p.val u₀.val := by
      intro i j hj
      exact (hb i j (Or.inl hj)).trans Matrix.one_apply.symm
    obtain ⟨x, u', hfix', hclear, he⟩ := column_factor p u₀ hfixed
    have hθ : (θ u' : ℂ) = 1 := by
      rw [entrywiseCharacter_apply_sum, Finset.sum_eq_zero, AddChar.map_zero_eq_one]
      intro i _
      by_cases hj : i.succ.val < p.val + 1
      · rw [hfix' _ _ hj, Matrix.one_apply, ite_eq_right (ne_of_lt i.castSucc_lt_succ)]
      · have hi : p.val ≤ i.castSucc.val := by simp at hj ⊢; omega
        rw [hclear, column_mul_entry, dite_eq_right (Nat.not_lt_of_le hi), add_zero]
        exact (hb _ _ (Or.inr hi)).trans (ite_eq_right (ne_of_lt i.castSucc_lt_succ))
    change ρ u₀.val (z 0) = z 0
    rw [he, Subgroup.coe_mul, rho_mul, hnext 0 u' hfix', hθ, one_smul,
      hcolumn, AddChar.zero_apply, one_smul]
  obtain ⟨χ, hχ⟩ : ∃ χ : AddChar A ℂ, z χ ≠ 0 := by
    by_contra! h
    have hsum : (∑ χ : AddChar A ℂ, z χ) = (Fintype.card A : ℂ) • v :=
      sum_additiveWeightSum σ v
    rw [Finset.sum_eq_zero (fun χ _ => h χ)] at hsum
    exact (smul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hv) hsum.symm
  obtain ⟨a, ha⟩ := rowCharacter_surjective (ι := Fin p.val) hψ χ
  have ha₀ : a ≠ 0 := by
    intro h
    subst a
    have hχ₀ : χ = 0 := ha.symm.trans (DFunLike.ext _ _ (fun x => by simp))
    exact hχ (hχ₀ ▸ hzero)
  obtain ⟨g, hg⟩ := exists_lastRow hp a ha₀
  let L := headLevi (k := k) p g
  let w := ρ L (z χ)
  have hw : w ≠ 0 := by
    intro he
    apply hχ
    have h := congrArg (ρ L⁻¹) he
    simpa only [w, ← rho_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] using h
  have hwNext : StageWeight ρ ψ (p.val + 1) w := by
    intro u hu
    obtain ⟨u', hu', hfix', ht⟩ := exists_headLevi_conj p g hu
    have he : u.val * L = L * u'.val := by rw [hu', ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    calc
      ρ u.val w = ρ L (ρ u'.val (z χ)) := by
        change ρ u.val (ρ L (z χ)) = _
        rw [← rho_mul, ← rho_mul, he]
      _ = (θ u : ℂ) • w := by
        rw [hnext χ u' hfix', entrywise_eq_of_fixedColumns ψ p hu hfix' ht, map_smul]
  have hwCol (y : A) : ρ (column p (Multiplicative.ofAdd y)).val w =
      (θ (column p (Multiplicative.ofAdd y)) : ℂ) • w := by
    obtain ⟨x, rfl⟩ : ∃ x : A, g.val.mulVec x = y :=
      ⟨(g⁻¹).val.mulVec y, by rw [Matrix.mulVec_mulVec, g.mul_inv, Matrix.one_mulVec]⟩
    have hrow : (g.val.mulVec x) (finalRow p.val hp) = a ⬝ᵥ x := by
      change (fun j => g.val (finalRow p.val hp) j) ⬝ᵥ x = a ⬝ᵥ x
      rw [hg]
    have hψx : χ x = ψ (a ⬝ᵥ x) := DFunLike.congr_fun ha.symm x
    calc
      ρ (column p (Multiplicative.ofAdd (g.val.mulVec x))).val w =
          ρ L (ρ (column p (Multiplicative.ofAdd x)).val (z χ)) := by
        change ρ _ (ρ L (z χ)) = _
        rw [← rho_mul, ← rho_mul]
        exact congrArg (fun h : GeneralLinear (n + 1) k => ρ h (z χ))
          (headLevi_mul_column p g x).symm
      _ = _ := by
        rw [hcolumn, map_smul, hψx, column_character ψ p hp, hrow]
  refine ⟨w, hw, ?_⟩
  intro u hu
  obtain ⟨x, u', hu', _, he⟩ := column_factor p u hu
  rw [he, Subgroup.coe_mul, rho_mul, hwNext u' hu', map_smul, hwCol, map_mul,
    Units.val_mul, smul_smul, mul_comm]

end WhittakerDescent

open WhittakerDescent in
/-- A nonzero cuspidal representation over a finite field has a nonzero vector in the
Whittaker eigenspace for each nontrivial additive character. -/
theorem IsCuspidal.whittakerVectors_ne_bot [Finite k]
    (ρ : Representation ℂ (GeneralLinear n k) V) (hρ : IsCuspidal ρ) (hn : 0 < n)
    (hV : ∃ v : V, v ≠ 0) {ψ : AddChar k ℂ} (hψ : ψ ≠ 0) :
    whittakerVectors ρ ψ ≠ ⊥ := by
  cases n with
  | zero => omega
  | succ n =>
    have hw : ∃ w : V, w ≠ 0 ∧ StageWeight ρ ψ 1 w := by
      refine Nat.decreasingInduction (motive := fun m _ =>
        0 < m → ∃ w : V, w ≠ 0 ∧ StageWeight ρ ψ m w) ?_ ?_ (Nat.succ_le_succ (Nat.zero_le n))
        (by omega)
      · intro m hm ih hm0
        obtain ⟨v, hv, hv'⟩ := ih (by omega)
        exact stageStep ρ hρ hψ ⟨m, hm⟩ hm0 v hv hv'
      · intro _
        obtain ⟨v, hv⟩ := hV
        refine ⟨v, hv, fun u hu => ?_⟩
        have he : u = 1 := Subtype.ext (Units.ext (Matrix.ext fun i j => hu i j j.isLt))
        simp [he]
    obtain ⟨w, hw, hw'⟩ := hw
    intro he
    apply hw
    have hmem : w ∈ whittakerVectors ρ ψ := by
      intro u
      apply hw' u
      intro i j hj
      have hj0 : j.val = 0 := by omega
      have hji : j ≤ i := show j.val ≤ i.val by omega
      rcases eq_or_lt_of_le hji with e | hji
      · subst j
        simp
      · rw [UpperUnipotent.entry_eq_zero u hji, Matrix.one_apply, ite_eq_right (ne_of_gt hji)]
    simpa [he] using hmem

end Langlands.FiniteGeneralLinear
