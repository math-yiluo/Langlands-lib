import Langlands.Algebra.FiniteOrderCongruenceProof
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # A congruence bound for orders of finite integral linear groups of rank six -/

noncomputable section

universe u

open scoped Matrix BigOperators

namespace Langlands

open FiniteOrderCongruence

private theorem reduceGL_injective_on_finite_group
    {n : ℕ} {Γ : Type u} [Group Γ] [Finite Γ]
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin n) ℤ) (hρ : Function.Injective ρ)
    (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective ((Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod m))).comp ρ) := by
  classical
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  let φ := (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ (Fin n → ℤ)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)
  have hφ : Function.Injective φ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ (Fin n → ℤ)).injective.comp
      (Matrix.GeneralLinearGroup.toLin.injective.comp hρ)
  let σ := (φ x).toAddEquiv
  have hv : ∀ v : Fin n → ℤ, σ v = (ρ x : Matrix (Fin n) (Fin n) ℤ) *ᵥ v := fun _ => rfl
  have hmtrx : (ρ x : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom (ZMod m)) = 1 :=
    congrArg Units.val hx
  have hmod (v : Fin n → ℤ) (i : Fin n) : (m : ℤ) ∣ σ v i - v i := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
    rw [hv]
    have hh := (Int.castRingHom (ZMod m)).map_mulVec (ρ x : Matrix (Fin n) (Fin n) ℤ) v i
    rw [hmtrx, Matrix.one_mulVec] at hh
    exact hh.symm
  have hσ : σ = AddEquiv.refl (Fin n → ℤ) := by
    apply finiteOrderCongruenceDetection (Fin n → ℤ) m hm ?_ σ ?_ ?_
    · rintro v ⟨k, hk, hz⟩
      have h : v = 0 := (smul_eq_zero.mp hz).resolve_left hk.ne'
      rw [h, smul_zero]
    · refine ⟨orderOf x, orderOf_pos x, ?_⟩
      have h : (φ x) ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      let f : ((Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) →* Equiv.Perm (Fin n → ℤ) :=
        { toFun := LinearEquiv.toEquiv
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      change (f (φ x)) ^ orderOf x = 1
      rw [← map_pow, h, map_one]
    · intro v
      choose w hw using (hmod v)
      refine ⟨w, ?_⟩
      ext i
      change σ v i = v i + m • w i
      rw [nsmul_eq_mul]
      exact sub_eq_iff_eq_add'.mp (hw i)
  apply hφ
  rw [map_one]
  apply LinearEquiv.ext
  intro v
  exact DFunLike.congr_fun hσ v

/-- A finite group admitting a faithful integral matrix representation of
rank six has order dividing `2^13 * 3^8 * 5 * 7`. -/
def FiniteIntegralRankSixGroupOrderStatement : Prop :=
  ∀ (Γ : Type u) [Group Γ] [Finite Γ]
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin 6) ℤ),
    Function.Injective ρ → Nat.card Γ ∣ 2 ^ 13 * 3 ^ 8 * 5 * 7

/-- Reduction modulo 3 and 7 and the finite general linear group order. -/
theorem finiteIntegralRankSixGroupOrder : FiniteIntegralRankSixGroupOrderStatement.{u} := by
  intro Γ _ _ ρ hρ
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h3 := Subgroup.card_dvd_of_injective _ (reduceGL_injective_on_finite_group ρ hρ 3 (by decide))
  have h7 := Subgroup.card_dvd_of_injective _ (reduceGL_injective_on_finite_group ρ hρ 7 (by decide))
  rw [Matrix.card_GL_field (𝔽 := ZMod 3) 6, ZMod.card] at h3
  rw [Matrix.card_GL_field (𝔽 := ZMod 7) 6, ZMod.card] at h7
  have hgcd : Nat.gcd (∏ i : Fin 6, (3 ^ 6 - 3 ^ i.val))
      (∏ i : Fin 6, (7 ^ 6 - 7 ^ i.val)) = 2 ^ 13 * 3 ^ 8 * 5 * 7 := by decide
  rw [← hgcd]
  exact Nat.dvd_gcd h3 h7


private theorem linearEquiv_eq_one_of_pow_seven_and_fixed_vector
    [Fact (Nat.Prime 3)]
    (f : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3))
    (hf : f ^ 7 = 1) (hfix : ∃ v, v ≠ 0 ∧ f v = v) : f = 1 := by
  classical
  let V := Fin 6 → ZMod 3
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F : V →ₗ[ZMod 3] V := f.toLinearMap - LinearMap.id
  let S := LinearMap.ker F
  let g : (V ≃ₗ[ZMod 3] V) →* Function.End V :=
    { toFun := fun e x => e x
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hg : (g f) ^ (7 ^ 1) = 1 := by rw [pow_one, ← map_pow, hf, map_one]
  have hcard := Equiv.Perm.card_fixedPoints_modEq hg
  let e : Function.fixedPoints (g f) ≃ S := Equiv.subtypeEquivRight (fun v => by
    change f v = v ↔ F v = 0
    simp only [F, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe])
  have hV : Fintype.card V = 3 ^ 6 := by simp [V]
  have hS : Fintype.card S = 3 ^ Module.finrank (ZMod 3) S := by
    rw [Module.card_eq_pow_finrank (K := ZMod 3) (V := S), ZMod.card]
  rw [Fintype.card_congr e, hV, hS] at hcard
  have h0 : 0 < Module.finrank (ZMod 3) S := by
    obtain ⟨v, hv, hfv⟩ := hfix
    apply Nat.pos_of_ne_zero
    intro h
    apply hv
    have hvS : v ∈ S := by
      change F v = 0
      simp only [F, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe, hfv]
    simpa only [Submodule.finrank_eq_zero.mp h, Submodule.mem_bot] using hvS
  have hVrank : Module.finrank (ZMod 3) V = 6 := by simp [V]
  have hle : Module.finrank (ZMod 3) S ≤ 6 := S.finrank_le.trans_eq hVrank
  have h6 : Module.finrank (ZMod 3) S = 6 := by
    have h : ∀ j : Fin 7, 0 < j.val → (3 ^ 6 : ℕ) ≡ 3 ^ j.val [MOD 7] → j.val = 6 := by decide
    exact h ⟨Module.finrank (ZMod 3) S, Nat.lt_succ_of_le hle⟩ h0 hcard
  have hsTop : S = ⊤ := Submodule.eq_top_of_finrank_eq (h6.trans hVrank.symm)
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ S := hsTop.symm ▸ Submodule.mem_top
  change F v = 0 at hv
  exact sub_eq_zero.mp hv

/-- An invariant line modulo three removes seven from the integral order bound. -/
def FiniteIntegralRankSixGroupOrderWithLineStatement : Prop :=
  ∀ (Γ : Type u) [Group Γ] [Finite Γ]
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin 6) ℤ), Function.Injective ρ →
    ∀ v : Fin 6 → ZMod 3, v ≠ 0 →
      (∀ g : Γ, ∃ a : ZMod 3,
        ((ρ g : Matrix (Fin 6) (Fin 6) ℤ).map (Int.castRingHom (ZMod 3))) *ᵥ v = a • v) →
    Nat.card Γ ∣ 2 ^ 13 * 3 ^ 8 * 5

theorem finiteIntegralRankSixGroupOrderWithLine : FiniteIntegralRankSixGroupOrderWithLineStatement.{u} := by
  classical
  intro Γ _ _ ρ hρ v hv hline
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hnd : ¬ 7 ∣ Nat.card Γ := by
    intro hd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 hd
    have hg7 : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
    let r := (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3))).comp ρ
    let V := Fin 6 → ZMod 3
    let φ := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp r)
    have hφ : Function.Injective φ :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V).injective.comp
        (Matrix.GeneralLinearGroup.toLin.injective.comp (reduceGL_injective_on_finite_group ρ hρ 3 (by decide)))
    let f := φ g
    have hf : f ^ 7 = 1 := by rw [← map_pow, hg7, map_one]
    obtain ⟨a, ha⟩ := hline g
    change f v = a • v at ha
    have hp (n : ℕ) : (f ^ n) v = a ^ n • v := by
      induction n with
      | zero => rw [pow_zero, pow_zero, one_smul]; rfl
      | succ n ih =>
        rw [pow_succ', pow_succ']
        change f ((f ^ n) v) = _
        rw [ih, map_smul, ha, mul_smul, smul_comm]
    have hp7 := hp 7
    rw [hf] at hp7
    change v = a ^ 7 • v at hp7
    have ha7 : a ^ 7 = (1 : ZMod 3) := by
      have he : (a ^ 7 - 1 : ZMod 3) • v = 0 := by rw [sub_smul, one_smul, ← hp7, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hv)
    have hu : ∀ a : ZMod 3, a ^ 7 = 1 → a = 1 := by decide
    have hfv : f v = v := by rw [ha, hu a ha7, one_smul]
    have hf1 := linearEquiv_eq_one_of_pow_seven_and_fixed_vector f hf ⟨v, hv, hfv⟩
    have hg1 : g = 1 := hφ (hf1.trans (map_one φ).symm)
    simp [hg1] at hg
  have hc : (Nat.card Γ).Coprime 7 :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr hnd |>.symm
  exact hc.dvd_of_dvd_mul_right (finiteIntegralRankSixGroupOrder Γ ρ hρ)

end Langlands
