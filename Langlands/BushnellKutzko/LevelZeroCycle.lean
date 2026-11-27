import Langlands.BushnellKutzko.LevelZeroSwapStep
import Langlands.BushnellKutzko.LevelZeroPerm

/-! # Injectivity of compression by a cyclic block permutation -/

open Matrix ValuativeRel Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF uV uW

section Cycle

variable {e : ℕ}

/-- The cycle `(0 1 … k)` of the first `k + 1` blocks, as a product of adjacent
transpositions. -/
def cyc : ℕ → Equiv.Perm (Fin e)
  | 0 => 1
  | k + 1 => if h : k + 1 < e then cyc k * Equiv.swap ⟨k, by omega⟩ ⟨k + 1, h⟩ else 1

theorem cyc_succ {k : ℕ} (h : k + 1 < e) :
    cyc (e := e) (k + 1) = cyc k * Equiv.swap ⟨k, by omega⟩ ⟨k + 1, h⟩ := by
  conv_lhs => unfold cyc
  simp [h]

theorem cyc_val {k : ℕ} (hk : k < e) (j : Fin e) :
    (cyc k j).val = if j.val < k then j.val + 1 else if j.val = k then 0 else j.val := by
  induction k generalizing j with
  | zero => simp [cyc]
  | succ k ih =>
    have hs : (Equiv.swap (⟨k, by omega⟩ : Fin e) ⟨k + 1, hk⟩ j).val =
        if j.val = k then k + 1 else if j.val = k + 1 then k else j.val := by
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.ext_iff] at * <;> omega
    rw [cyc_succ hk, Equiv.Perm.mul_apply, ih (by omega), hs]
    split_ifs <;> omega

theorem cyc_self {k : ℕ} (hk : k < e) : cyc k ⟨k, hk⟩ = ⟨0, by omega⟩ := by
  ext; rw [cyc_val hk]; simp

theorem cyc_succ_apply {k : ℕ} (hk : k + 1 < e) : cyc k ⟨k + 1, hk⟩ = ⟨k + 1, hk⟩ := by
  ext; rw [cyc_val (by omega)]; simp

end Cycle

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e f : ℕ}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem permGL_inv (w : Equiv.Perm (Fin e)) :
    permGL F (f := f) w⁻¹ = (permGL F w)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← permGL_mul, inv_mul_cancel, permGL_one]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin f × Fin e) F) V) (hπ : IsSmooth π)
  (K : OpenSubgroup (GL (Fin f × Fin e) F)) (hK : IsCompact (K : Set (GL (Fin f × Fin e) F)))

variable [Fintype 𝓀[F]]

/-- **Injectivity of compression by the cycle of the first `k + 1` blocks.** Let `f` be an
intertwining map from a representation `ρ` of `U(𝔄)`, trivial on `U^1(𝔄) = K`, whose
restriction to the first block is cuspidal in the form of vanishing sums over lifted unipotent
radicals. Then compression of `f` by the permutation matrix of `(cyc k)⁻¹` vanishes only when
`f` vanishes. -/
theorem compressionMap_cyc_comp_eq_zero (he : 0 < e) (hKJ : K.toSubgroup = J1 F e f)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (J0 F e f) W)
    (hρ1 : ∀ x : J0 F e f, (x : GL (Fin f × Fin e) F) ∈ J1 F e f → ρ x = 1)
    (hcusp : ∀ (m : Fin e) (hm : (⟨0, he⟩ : Fin e) < m) (r : ℕ), 0 < r → r < f →
      ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F],
        ρ ⟨pairGL hm.ne (diagU (unipLift r Z) 1),
          diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one⟩ = 0)
    (φ : W →ₗ[ℂ] V) (hφ : ∀ (x : J0 F e f) (w : W), φ (ρ x w) = π x (φ w)) :
    ∀ k, k < e → (compressionMap π hπ K hK (permGL F (cyc k)⁻¹)).comp φ = 0 → φ = 0 := by
  classical
  have hJK : ∀ x, x ∈ K ↔ x ∈ J1 F e f := fun x => by
    change x ∈ K.toSubgroup ↔ _; rw [hKJ]
  have hmemK : ∀ x, x ∈ J1 F e f → x ∈ K := fun x hx => (hJK x).mpr hx
  have hφfix : ∀ w, φ w ∈ fixedVectors π K.toSubgroup := by
    intro w k
    have hk : (k : GL (Fin f × Fin e) F) ∈ J1 F e f := (hJK k.val).mp k.property
    change π k (φ w) = φ w
    rw [← hφ ⟨k, J1_le_J0 hk⟩, hρ1 _ hk]
    rfl
  have hnorm : ∀ x ∈ J0 F e f, ∀ y, y ∈ K ↔ x⁻¹ * y * x ∈ K := by
    intro x hx y
    change y ∈ K.toSubgroup ↔ x⁻¹ * y * x ∈ K.toSubgroup
    rw [hKJ]
    exact mem_J1_iff_conj hx y
  intro k
  induction k with
  | zero =>
    intro _ h
    ext w
    have h1 := LinearMap.congr_fun h w
    simp only [cyc, inv_one, permGL_one, LinearMap.comp_apply, compressionMap_apply, map_one,
      Module.End.one_apply, LinearMap.zero_apply] at h1
    rwa [Compact.averageMap_id π hπ K hK _ (hφfix w)] at h1
  | succ m ih =>
    intro hm h
    have hm0 : m < e := by omega
    let i : Fin e := ⟨m, hm0⟩
    let j : Fin e := ⟨m + 1, hm⟩
    have hij : i.val + 1 = j.val := rfl
    have hlt : i < j := by rw [Fin.lt_def]; simp [i, j]
    have h0j : (⟨0, he⟩ : Fin e) < j := by rw [Fin.lt_def]; simp [j]
    set y : GL (Fin f × Fin e) F := permGL F (cyc m)⁻¹ with hy
    set S : GL (Fin f × Fin e) F := pairGL hlt.ne swapU with hS
    -- conjugating the two-block elements of the blocks `m, m + 1` by `y`
    have hyinv : y⁻¹ = permGL F (cyc m) := by rw [hy, permGL_inv, inv_inv]
    have hy' : y = (permGL F (cyc m))⁻¹ := by rw [← hyinv, inv_inv]
    have hconj : ∀ u : GL (Fin f ⊕ Fin f) F,
        y⁻¹ * pairGL hlt.ne u * y = pairGL h0j.ne u := by
      intro u
      rw [hyinv, hy', permGL_conj_pairGL]
      exact pairGL_eq_of_eq _ _ (cyc_self hm0) (cyc_succ_apply hm) u
    -- multiplicativity of compression
    have hmul : ∀ v ∈ fixedVectors π K.toSubgroup,
        compressionMap π hπ K hK S (compressionMap π hπ K hK y v) =
          compressionMap π hπ K hK (permGL F (cyc (m + 1))⁻¹) v := by
      intro v hv
      have hprod : S * y = permGL F (cyc (m + 1))⁻¹ := by
        rw [hS, hy, ← permGL_swap, ← permGL_mul, cyc_succ hm, _root_.mul_inv_rev,
          Equiv.swap_inv]
      rw [← hprod]
      refine compressionMap_mul_of_factor π hπ K hK S y ?_ v hv
      intro κ hκ
      have hκJ : κ ∈ J1 F e f := (hJK κ).mp hκ
      let Y : Matrix (Fin f) (Fin f) F := fun a b => (κ : Matrix _ _ F) (a, j) (b, i)
      have hYint : ∀ a b, valuation F (Y a b) ≤ 1 := fun a b => (hκJ.1.1 _ _).1
      set l : GL (Fin f × Fin e) F := pairGL hlt.ne (lowerU Y) with hl
      have hlJ : l ∈ J1 F e f := lowerU_mem_J1 hlt hYint
      refine ⟨κ * l⁻¹, l, by group, ?_, ?_⟩
      · have huJ : κ * l⁻¹ ∈ J1 F e f := (J1 F e f).mul_mem hκJ ((J1 F e f).inv_mem hlJ)
        have hθ : (⟨κ * l⁻¹, huJ⟩ : J1 F e f) ∈ (thetaHom hij).ker := by
          rw [MonoidHom.mem_ker]
          have : (⟨κ * l⁻¹, huJ⟩ : J1 F e f) = ⟨κ, hκJ⟩ * (⟨l, hlJ⟩ : J1 F e f)⁻¹ := rfl
          rw [this, map_mul, map_inv, mul_inv_eq_one]
          apply Multiplicative.toAdd.injective
          ext a b
          change res ((κ : Matrix _ _ F) (a, j) (b, i)) =
            res (pairEmb F hlt.ne (fromBlocks 1 0 Y 1) (a, j) (b, i))
          rw [pairEmb_rl, Matrix.fromBlocks_apply₂₁]
        have := swap_conj_mem_J1 hij hθ
        have hSinv : S⁻¹ = S := by rw [hS, ← map_inv, swapU_inv]
        rw [hSinv]
        exact hmemK _ this
      · rw [hl, hconj]
        exact hmemK _ (lowerU_mem_J1 h0j hYint)
    -- the composed map
    set g : W →ₗ[ℂ] V := (compressionMap π hπ K hK y).comp φ with hg
    have hgfix : ∀ w, g w ∈ fixedVectors π K.toSubgroup := fun w =>
      Compact.averageMap_mem_fixedVectors π hπ K hK _
    have hzero : (compressionMap π hπ K hK S).comp g = 0 := by
      ext w
      rw [LinearMap.comp_apply, hg, LinearMap.comp_apply, hmul _ (hφfix w)]
      exact LinearMap.congr_fun h w
    let τ : GL (Fin f) F → GL (Fin f) F → Module.End ℂ W := fun A D =>
      if hAD : IsIntGL A ∧ IsIntGL D then
        ρ ⟨pairGL h0j.ne (diagU A D), diagU_mem_J0 h0j hAD.1 hAD.2⟩ else 0
    have hτ : ∀ A D, IsIntGL A → IsIntGL D → ∀ w,
        g (τ A D w) = π (pairGL hlt.ne (diagU A D)) (g w) := by
      intro A D hA hD w
      have hx := diagU_mem_J0 hlt hA hD
      simp only [τ, hA, hD, and_self, dite_true]
      rw [hg, LinearMap.comp_apply, LinearMap.comp_apply, hφ, compressionMap_apply,
        compressionMap_apply, ← averageMap_apply_normalizing π hπ K hK _ (hnorm _ hx)]
      congr 1
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      change y * pairGL h0j.ne (diagU A D) = pairGL hlt.ne (diagU A D) * y
      rw [← hconj]
      group
    have hcusp' : ∀ r, 0 < r → r < f →
        ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F], τ (unipLift r Z) 1 = 0 := by
      intro r hr0 hrf
      have h1 : ∀ Z : Matrix (Fin f) (Fin f) 𝓀[F], τ (unipLift r Z) 1 =
          ρ ⟨pairGL h0j.ne (diagU (unipLift r Z) 1),
            diagU_mem_J0 h0j (isIntGL_unipLift r Z) isIntGL_one⟩ := by
        intro Z
        simp only [τ, isIntGL_unipLift r Z, isIntGL_one, and_self, dite_true]
      simp only [h1]
      exact hcusp j h0j r hr0 hrf
    have hg0 := compressionMap_swap_comp_eq_zero π hπ K hK hij hlt hKJ g hgfix τ hτ hcusp' hzero
    exact ih hm0 hg0

end Langlands.BushnellKutzko.LevelZero
