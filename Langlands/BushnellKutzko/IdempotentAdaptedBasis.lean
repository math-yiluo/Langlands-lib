import Langlands.BushnellKutzko.IdempotentIwahoriFactorization
import Langlands.Representation.Classification.SupercuspidalDerivativeVanishing

/-! # Two-block parabolics attached to an idempotent -/

noncomputable section

namespace Langlands.BushnellKutzko.BlockIdempotent

open Langlands.GeneralLinear Langlands.Classification.SupercuspidalDerivativeVanishing

universe uF

variable {F : Type uF} [Field F]

/-- A basis of `F^(a+c)` whose first `a` vectors lie in the range of the idempotent `ε` and whose
last `c` vectors lie in its kernel, when the range has dimension `a`. -/
theorem exists_adapted_basis {a c : ℕ} {ε : Module.End F (Fin (a + c) → F)}
    (he : IsIdempotentElem ε) (hr : Module.finrank F (LinearMap.range ε) = a) :
    ∃ b : Module.Basis (Fin (a + c)) F (Fin (a + c) → F),
      (∀ i : Fin a, ε (b (Fin.castAdd c i)) = b (Fin.castAdd c i)) ∧
      ∀ j : Fin c, ε (b (Fin.natAdd a j)) = 0 := by
  have hc := LinearMap.IsIdempotentElem.isCompl he
  have hk : Module.finrank F (LinearMap.ker ε) = c := by
    have h := Submodule.finrank_add_eq_of_isCompl hc
    rw [hr, Module.finrank_fin_fun] at h
    omega
  let b1 := Module.finBasisOfFinrankEq F (LinearMap.range ε) hr
  let b2 := Module.finBasisOfFinrankEq F (LinearMap.ker ε) hk
  let b := ((b1.prod b2).map (Submodule.prodEquivOfIsCompl _ _ hc)).reindex finSumFinEquiv
  refine ⟨b, fun i => ?_, fun j => ?_⟩
  · have hb : b (Fin.castAdd c i) = (b1 i : Fin (a + c) → F) := by
      simp [b, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
    rw [hb]
    exact (LinearMap.IsIdempotentElem.mem_range_iff he).mp (b1 i).property
  · have hb : b (Fin.natAdd a j) = (b2 j : Fin (a + c) → F) := by
      simp [b, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
    rw [hb]
    exact (b2 j).property

/-- **The two-block parabolic of an idempotent.** If the range of the idempotent `ε` of
`F^(a+c)` has dimension `a`, some `g ∈ GL_(a+c)(F)` conjugates every block unipotent matrix
`[[1_a, *], [0, 1_c]]` into the unipotent radical `upperGroup ε`. -/
theorem exists_conj_mem_upperGroup {a c : ℕ} {ε : Module.End F (Fin (a + c) → F)}
    (he : IsIdempotentElem ε) (hr : Module.finrank F (LinearMap.range ε) = a) :
    ∃ g : GeneralLinear (a + c) F, ∀ X : GeneralLinear (a + c) F, IsBlockUnipotent a X →
      Matrix.GeneralLinearGroup.toLin (g * X * g⁻¹) ∈ upperGroup ε := by
  classical
  obtain ⟨b, hb1, hb0⟩ := exists_adapted_basis (c := c) he hr
  have hε1 : ∀ r : Fin (a + c), r.val < a → ε (b r) = b r := by
    intro r hr'
    have : r = Fin.castAdd c ⟨r.val, hr'⟩ := Fin.ext rfl
    rw [this]
    exact hb1 _
  have hε0 : ∀ r : Fin (a + c), a ≤ r.val → ε (b r) = 0 := by
    intro r hr'
    have : r = Fin.natAdd a ⟨r.val - a, by omega⟩ := Fin.ext (by simp; omega)
    rw [this]
    exact hb0 _
  let T : (Fin (a + c) → F) ≃ₗ[F] (Fin (a + c) → F) :=
    (Pi.basisFun F (Fin (a + c))).equiv b (Equiv.refl _)
  let Tu := LinearMap.GeneralLinearGroup.ofLinearEquiv T
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm Tu, fun X hX => ?_⟩
  have hT : ∀ s, T (Pi.single s 1) = b s := by
    intro s
    have := (Pi.basisFun F (Fin (a + c))).equiv_apply s b (Equiv.refl _)
    simpa using this
  have hTinv : ∀ s, T.symm (b s) = Pi.single s 1 := by
    intro s
    rw [← hT s, LinearEquiv.symm_apply_apply]
  have hXv : ∀ s, (Matrix.GeneralLinearGroup.toLin X : Module.End F (Fin (a + c) → F))
      (Pi.single s 1) = ∑ r, X r s • Pi.single r (1 : F) := by
    intro s
    rw [Matrix.GeneralLinearGroup.toLin_apply]
    ext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
  have hconj : ∀ s, ((Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.toLin.symm Tu * X * (Matrix.GeneralLinearGroup.toLin.symm Tu)⁻¹)
      : Module.End F (Fin (a + c) → F))) (b s) = ∑ r, X r s • b r := by
    intro s
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    change T ((Matrix.GeneralLinearGroup.toLin X : Module.End F (Fin (a + c) → F))
      (T.symm (b s))) = _
    rw [hTinv, hXv, map_sum]
    simp only [map_smul, hT]
  refine ⟨?_, ?_⟩
  · refine b.ext fun s => ?_
    rw [Module.End.mul_apply]
    by_cases hs : s.val < a
    · rw [hε1 s hs, hconj]
      rw [Finset.sum_eq_single s]
      · have h1 : X s s = 1 := by simpa using hX s s (Or.inl hs)
        rw [h1, one_smul]
      · intro r _ hrs
        have h0 : X r s = 0 := by simpa [hrs] using hX r s (Or.inl hs)
        rw [h0, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ s) h
    · rw [hε0 s (by omega), map_zero]
  · refine b.ext fun s => ?_
    rw [Module.End.mul_apply, hconj, map_sum]
    have hterm : ∀ r, (1 - ε) (X r s • b r) =
        if r = s then (1 - ε) (b r) else 0 := by
      intro r
      rw [map_smul, LinearMap.sub_apply, Module.End.one_apply]
      by_cases hr' : r.val < a
      · rw [hε1 r hr', sub_self, smul_zero]
        split_ifs <;> rfl
      · have hrv := hX r s (Or.inr (by omega))
        split_ifs with hrs
        · subst hrs
          rw [show X r r = 1 by simpa using hrv, one_smul]
        · rw [show X r s = 0 by simpa [hrs] using hrv, zero_smul]
    rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_ite_eq' Finset.univ s]
    simp

/-- **A proper two-block parabolic attached to an idempotent.** For an idempotent `ε` of
`F^n` different from `0` and `1` there are a two-block shape `B` with `B.parabolic F ≠ ⊤` and
`g ∈ GL_n(F)` such that every element of `B.conjugateUnipotent g` lies in `upperGroup ε`. -/
theorem exists_blockShape {n : ℕ} {ε : Module.End F (Fin n → F)} (he : IsIdempotentElem ε)
    (h0 : ε ≠ 0) (h1 : ε ≠ 1) :
    ∃ (B : BlockShape n) (g : GeneralLinear n F), B.parabolic F ≠ ⊤ ∧
      ∀ x ∈ B.conjugateUnipotent g, Matrix.GeneralLinearGroup.toLin x ∈ upperGroup ε := by
  obtain ⟨a, ha⟩ : ∃ a, Module.finrank F (LinearMap.range ε) = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, Module.finrank F (LinearMap.ker ε) = c := ⟨_, rfl⟩
  have hsum : a + c = n := by
    have h := LinearMap.finrank_range_add_finrank_ker ε
    rw [ha, hc, Module.finrank_fin_fun] at h
    exact h
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      apply h0
      rw [h, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at ha
      exact ha
    · exact h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exfalso
      apply h1
      rw [h, Submodule.finrank_eq_zero] at hc
      have hinj : Function.Injective ε := LinearMap.ker_eq_bot.mp hc
      refine LinearMap.ext fun v => ?_
      apply hinj
      change (ε * ε) v = ε v
      rw [he.eq]
    · exact h
  subst hsum
  obtain ⟨g, hg⟩ := exists_conj_mem_upperGroup (c := c) he ha
  refine ⟨BlockShape.binary a c ha0 hc0, g, binary_parabolic_ne_top ha0 hc0, ?_⟩
  rintro x ⟨X, hX, rfl⟩
  exact hg X (isBlockUnipotent_of_mem_binary ha0 hc0 hX)

end Langlands.BushnellKutzko.BlockIdempotent
