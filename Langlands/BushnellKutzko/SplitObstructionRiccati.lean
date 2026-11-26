import Langlands.BushnellKutzko.SplitObstructionLattice
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Block triangularization by successive approximation

Let `ε₁, ε₂` be complementary idempotents in the order of an `𝔬_F`-lattice chain, nonzero,
and let `γ ∈ A = End_F(V)`. Suppose the block commutator `x ↦ (ε₁γε₁)x − x(ε₂γε₂)` on the
off-diagonal block `ε₁Aε₂` maps the `j`-th filtration step onto the `(j−r)`-th, that
`ε₂γε₁ ∈ 𝔓^{−r}`, and that `ε₁γε₂` is the image of an element of the first step modulo the
`(1−r)`-th step. Then conjugation by `1 + t`, for a suitable `t ∈ 𝔓 ∩ ε₁Aε₂`, makes the
`(1,2)`-block of `γ` vanish, and `F[γ]` is not a field.

This is the successive-approximation argument at the end of the proof of
Bushnell–Kutzko (1993), (2.3.12), printed pp. 63–64, organised as a contraction on the
first filtration step of the off-diagonal block, followed by the argument of (2.3.5),
printed p. 59, in the form: an `F[γ]`-linear map of a vector space over a field `F[γ]`
would give a nonzero element of the kernel of the block commutator.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitObstruction

universe uF uV

section Idempotents

variable {R : Type*} [Ring R] {ε₁ ε₂ : R}

/-- Complementary idempotents: the product in the other order also vanishes. -/
theorem mul_eq_zero_of_complement (hsum : ε₁ + ε₂ = 1) (h12 : ε₁ * ε₂ = 0) : ε₂ * ε₁ = 0 := by
  have h2 : ε₂ = 1 - ε₁ := by rw [← hsum]; abel
  have h1 : ε₁ * ε₁ = ε₁ := by
    have h := h12
    rw [h2, mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm
  rw [h2, sub_mul, one_mul, h1, sub_self]

theorem idempotent_left_of_complement (hsum : ε₁ + ε₂ = 1) (h12 : ε₁ * ε₂ = 0) :
    ε₁ * ε₁ = ε₁ := by
  have h2 : ε₂ = 1 - ε₁ := by rw [← hsum]; abel
  have h := h12
  rw [h2, mul_sub, mul_one, sub_eq_zero] at h
  exact h.symm

theorem idempotent_right_of_complement (hsum : ε₁ + ε₂ = 1) (h12 : ε₁ * ε₂ = 0) :
    ε₂ * ε₂ = ε₂ := by
  have h1 : ε₁ = 1 - ε₂ := by rw [← hsum]; abel
  have h21 := mul_eq_zero_of_complement hsum h12
  rw [h1, mul_sub, mul_one, sub_eq_zero] at h21
  exact h21.symm

end Idempotents

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

/-- The block commutator `x ↦ (ε₁γε₁) x − x (ε₂γε₂)`. -/
def blockCommutator (ε₁ ε₂ γ : A) : A →ₗ[F] A :=
  LinearMap.mulLeft F (ε₁ * γ * ε₁) - LinearMap.mulRight F (ε₂ * γ * ε₂)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockCommutator_apply (ε₁ ε₂ γ x : A) :
    blockCommutator ε₁ ε₂ γ x = ε₁ * γ * ε₁ * x - x * (ε₂ * γ * ε₂) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- **Block triangularization.** Under graded surjectivity of the block commutator on the
off-diagonal block, the algebra `F[γ]` is not a field. -/
theorem not_isField_of_blockCommutator {ε₁ ε₂ γ : A} {r : ℤ}
    (hsum : ε₁ + ε₂ = 1) (h12 : ε₁ * ε₂ = 0) (hε₁ : ε₁ ∈ P 0) (hε₂ : ε₂ ∈ P 0)
    (hne₁ : ε₁ ≠ 0) (hne₂ : ε₂ ≠ 0) (hz : ε₂ * γ * ε₁ ∈ P (-r))
    (hD : ∀ j : ℤ, ∀ w ∈ blockFiltration 𝓛 ε₁ ε₂ (j - r),
      ∃ x ∈ blockFiltration 𝓛 ε₁ ε₂ j, blockCommutator ε₁ ε₂ γ x = w)
    (hy : ∃ x ∈ blockFiltration 𝓛 ε₁ ε₂ 1,
      ε₁ * γ * ε₂ - blockCommutator ε₁ ε₂ γ x ∈ blockFiltration 𝓛 ε₁ ε₂ (1 - r)) :
    ¬ IsField (elementAlgebra γ) := by
  classical
  have := 𝓛.finiteDimensional
  set D := blockCommutator ε₁ ε₂ γ with hDdef
  set W := offDiagonal ε₁ ε₂ with hWdef
  set z := ε₂ * γ * ε₁ with hzdef
  have h21 : ε₂ * ε₁ = 0 := mul_eq_zero_of_complement hsum h12
  have h11 : ε₁ * ε₁ = ε₁ := idempotent_left_of_complement hsum h12
  have h22 : ε₂ * ε₂ = ε₂ := idempotent_right_of_complement hsum h12
  -- elementary facts about the off-diagonal block
  have hW1 : ∀ x ∈ W, ε₁ * x = x := by
    intro x hx
    have hx' : ε₁ * x * ε₂ = x := hx
    rw [← hx', ← mul_assoc, ← mul_assoc, h11]
  have hW2 : ∀ x ∈ W, x * ε₂ = x := by
    intro x hx
    have hx' : ε₁ * x * ε₂ = x := hx
    rw [← hx', mul_assoc, h22]
  have hW3 : ∀ x ∈ W, x * ε₁ = 0 := by
    intro x hx
    rw [← hW2 x hx, mul_assoc, h21, mul_zero]
  have hW4 : ∀ x ∈ W, ε₂ * x = 0 := by
    intro x hx
    rw [← hW1 x hx, ← mul_assoc, h21, zero_mul]
  have hWmem : ∀ x : A, ε₁ * x = x → x * ε₂ = x → x ∈ W := by
    intro x h1 h2
    change ε₁ * x * ε₂ = x
    rw [h1, h2]
  have hDW : ∀ x ∈ W, D x ∈ W := by
    intro x hx
    apply hWmem
    · rw [hDdef, blockCommutator_apply, mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc, h11,
        ← mul_assoc, hW1 x hx]
    · rw [hDdef, blockCommutator_apply, sub_mul, mul_assoc _ x ε₂, hW2 x hx, mul_assoc x,
        mul_assoc _ γ ε₂, mul_assoc ε₂ (γ * ε₂), mul_assoc γ ε₂ ε₂, h22]
  -- the restriction of the block commutator to `W` is bijective
  let DW : W →ₗ[F] W := D.restrict hDW
  have hDWapply : ∀ x : W, ((DW x : W) : A) = D x := fun x => rfl
  have hsurj : Function.Surjective DW := by
    intro w
    obtain ⟨k, hk⟩ := exists_mem_endFiltration 𝓛 (w : A)
    have hwM : (w : A) ∈ blockFiltration 𝓛 ε₁ ε₂ ((k + r) - r) :=
      ⟨by rwa [add_sub_cancel_right], w.2⟩
    obtain ⟨x, hx, hxw⟩ := hD (k + r) w hwM
    exact ⟨⟨x, hx.2⟩, Subtype.ext hxw⟩
  have hinj : Function.Injective DW := LinearMap.injective_iff_surjective.mpr hsurj
  let e : W ≃ₗ[F] W := LinearEquiv.ofBijective DW ⟨hinj, hsurj⟩
  have he : ∀ x : W, e x = DW x := fun x => rfl
  have hbound : ∀ (j : ℤ) (w : W), (w : A) ∈ P (j - r) → ((e.symm w : W) : A) ∈ P j := by
    intro j w hw
    obtain ⟨x, hx, hxw⟩ := hD j w ⟨hw, w.2⟩
    have hxe : e ⟨x, hx.2⟩ = w := Subtype.ext hxw
    rw [← hxe, LinearEquiv.symm_apply_apply]
    exact hx.1
  -- the quadratic term
  have hqW : ∀ t : A, t ∈ W → t * z * t ∈ W := by
    intro t ht
    apply hWmem
    · rw [← mul_assoc, ← mul_assoc, hW1 t ht]
    · rw [mul_assoc, hW2 t ht]
  let y : W := ⟨ε₁ * γ * ε₂, hWmem _ (by rw [← mul_assoc, ← mul_assoc, h11])
    (by rw [mul_assoc, h22])⟩
  let q : W → W := fun t => ⟨(t : A) * z * t, hqW t t.2⟩
  let Φ : W → W := fun t => e.symm (y - q t)
  -- estimates for `Φ`
  obtain ⟨x₀, hx₀, hx₀y⟩ := hy
  have hey : ((e.symm y : W) : A) ∈ P 1 := by
    have hdiff : y - DW ⟨x₀, hx₀.2⟩ ∈ (⊤ : Submodule F W) := Submodule.mem_top
    have hb := hbound 1 (y - DW ⟨x₀, hx₀.2⟩) (by
      change ε₁ * γ * ε₂ - D x₀ ∈ P (1 - r)
      exact hx₀y.1)
    rw [map_sub, ← he, LinearEquiv.symm_apply_apply] at hb
    have := add_mem hb hx₀.1
    simpa using this
  have hq : ∀ t : W, (t : A) ∈ P 1 → ((q t : W) : A) ∈ P (2 - r) := by
    intro t ht
    have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration ht hz) ht
    exact 𝓛.endFiltration_antitone (by omega) h
  have hΦ1 : ∀ t : W, (t : A) ∈ P 1 → ((Φ t : W) : A) ∈ P 1 := by
    intro t ht
    have h2 := hbound 2 (q t) (hq t ht)
    change ((e.symm (y - q t) : W) : A) ∈ P 1
    rw [map_sub, Submodule.coe_sub]
    exact sub_mem hey (𝓛.endFiltration_antitone (by omega) h2)
  have hΦ2 : ∀ (t t' : W) (m : ℤ), (t : A) ∈ P 1 → (t' : A) ∈ P 1 →
      ((t : A) - t') ∈ P m → ((Φ t : W) : A) - Φ t' ∈ P (m + 1) := by
    intro t t' m ht ht' htt'
    have hsub : (Φ t : W) - Φ t' = e.symm (q t' - q t) := by
      simp only [Φ, ← map_sub]
      congr 1
      abel
    rw [← Submodule.coe_sub, hsub]
    apply hbound (m + 1)
    change (t' : A) * z * t' - t * z * t ∈ P (m + 1 - r)
    have heq : (t' : A) * z * t' - t * z * t = -(((t : A) - t') * z * t' + t * z * (t - t')) := by
      noncomm_ring
    rw [heq]
    apply neg_mem
    apply add_mem
    · have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration htt' hz) ht'
      exact 𝓛.endFiltration_antitone (by omega) h
    · have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration ht hz) htt'
      exact 𝓛.endFiltration_antitone (by omega) h
  -- the iteration
  let seq : ℕ → W := fun k => Φ^[k] 0
  have hseq_succ : ∀ k, seq (k + 1) = Φ (seq k) := fun k =>
    Function.iterate_succ_apply' Φ k 0
  have hseq1 : ∀ k, ((seq k : W) : A) ∈ P 1 := by
    intro k
    induction k with
    | zero => exact zero_mem _
    | succ k ih => rw [hseq_succ]; exact hΦ1 _ ih
  have hseq2 : ∀ k : ℕ, ((seq (k + 1) : W) : A) - seq k ∈ P (1 + k) := by
    intro k
    induction k with
    | zero =>
      have h := hΦ1 0 (zero_mem _)
      simpa [seq] using h
    | succ k ih =>
      have h := hΦ2 (seq (k + 1)) (seq k) (1 + k) (hseq1 _) (hseq1 _) ih
      have hk : ((seq (k + 1) : W) : A) = Φ (seq k) := congrArg Subtype.val (hseq_succ k)
      have heq : ((seq (k + 1 + 1) : W) : A) - seq (k + 1) = Φ (seq (k + 1)) - Φ (seq k) := by
        rw [hseq_succ (k + 1), ← hk]
      rw [heq]
      push_cast
      convert h using 2
      ring
  obtain ⟨L, hL1, hLlim⟩ := exists_limit 𝓛 (c := 1) (fun k => ((seq k : W) : A)) hseq1 hseq2
  -- the limit lies in the off-diagonal block
  have hLW : L ∈ W := by
    have h0 : ε₁ * L * ε₂ - L = 0 := by
      apply eq_zero_of_forall_ge_mem 𝓛 (k₀ := 1)
      intro k
      have hk := hLlim k
      have hsk : ε₁ * ((seq k : W) : A) * ε₂ = seq k := (seq k).2
      have heq : ε₁ * L * ε₂ - L = ε₁ * (L - seq k) * ε₂ - (L - seq k) := by
        rw [mul_sub, sub_mul, hsk]
        abel
      rw [heq]
      apply sub_mem _ hk
      have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hε₁ hk) hε₂
      exact 𝓛.endFiltration_antitone (by omega) h
    exact sub_eq_zero.mp h0
  let Lw : W := ⟨L, hLW⟩
  -- the limit is a fixed point
  have hfix : Φ Lw = Lw := by
    apply Subtype.ext
    have h0 : ((Φ Lw : W) : A) - L = 0 := by
      apply eq_zero_of_forall_ge_mem 𝓛 (k₀ := 2)
      intro k
      have h1 := hΦ2 Lw (seq k) (1 + k) hL1 (hseq1 k) (hLlim k)
      have h2 := hLlim (k + 1)
      rw [← hseq_succ] at h1
      have heq : ((Φ Lw : W) : A) - L = (((Φ Lw : W) : A) - seq (k + 1)) - (L - seq (k + 1)) := by
        abel
      rw [heq]
      apply sub_mem
      · exact 𝓛.endFiltration_antitone (by omega) h1
      · exact 𝓛.endFiltration_antitone (by push_cast; omega) h2
    exact sub_eq_zero.mp h0
  have hRic : D L = ε₁ * γ * ε₂ - L * z * L := by
    have h := congrArg e hfix
    rw [LinearEquiv.apply_symm_apply] at h
    have h' := congrArg Subtype.val h
    rw [he, hDWapply] at h'
    exact h'.symm
  -- the conjugation
  have hL1' : ε₁ * L = L := hW1 L hLW
  have hL2' : L * ε₂ = L := hW2 L hLW
  have hLε₁ : L * ε₁ = 0 := hW3 L hLW
  have hε₂L : ε₂ * L = 0 := hW4 L hLW
  have hLL : L * L = 0 := by
    calc L * L = (L * ε₂) * L := by rw [hL2']
      _ = L * (ε₂ * L) := mul_assoc _ _ _
      _ = 0 := by rw [hε₂L, mul_zero]
  set γ' := (1 + L) * γ * (1 - L) with hγ'
  have hK1 : ε₁ * γ' * ε₂ = 0 := by
    have hA : ε₁ * γ' * ε₂ = (ε₁ + L) * γ * (ε₂ - L) := by
      rw [hγ', show ε₁ * ((1 + L) * γ * (1 - L)) * ε₂ = (ε₁ * (1 + L)) * γ * ((1 - L) * ε₂) by
        simp only [mul_assoc]]
      rw [mul_add, mul_one, hL1', sub_mul, one_mul, hL2']
    have hB : (ε₁ + L) * γ * (ε₂ - L) =
        ε₁ * γ * ε₂ - ε₁ * γ * L + L * γ * ε₂ - L * γ * L := by noncomm_ring
    have hC : ε₁ * γ * L = ε₁ * γ * ε₁ * L := by rw [mul_assoc (ε₁ * γ) ε₁ L, hL1']
    have hC' : L * γ * ε₂ = L * (ε₂ * γ * ε₂) := by
      rw [show L * (ε₂ * γ * ε₂) = (L * ε₂) * γ * ε₂ by simp only [mul_assoc], hL2']
    have hC'' : L * γ * L = L * z * L := by
      rw [hzdef, show L * (ε₂ * γ * ε₁) * L = (L * ε₂) * γ * (ε₁ * L) by simp only [mul_assoc],
        hL2', hL1']
    rw [hA, hB, hC, hC', hC'']
    have hR : D L = ε₁ * γ * ε₁ * L - L * (ε₂ * γ * ε₂) := blockCommutator_apply _ _ _ _
    rw [show ε₁ * γ * ε₂ - ε₁ * γ * ε₁ * L + L * (ε₂ * γ * ε₂) - L * z * L =
      ε₁ * γ * ε₂ - (ε₁ * γ * ε₁ * L - L * (ε₂ * γ * ε₂)) - L * z * L by abel, ← hR, hRic]
    abel
  have hK2 : ε₁ * γ' * ε₁ = ε₁ * γ * ε₁ + L * z := by
    rw [hγ', show ε₁ * ((1 + L) * γ * (1 - L)) * ε₁ = (ε₁ * (1 + L)) * γ * ((1 - L) * ε₁) by
      simp only [mul_assoc]]
    rw [mul_add, mul_one, hL1', sub_mul, one_mul, hLε₁, sub_zero, add_mul, add_mul, hzdef]
    congr 1
    rw [show L * (ε₂ * γ * ε₁) = (L * ε₂) * γ * ε₁ by simp only [mul_assoc], hL2']
  have hK3 : ε₂ * γ' * ε₂ = ε₂ * γ * ε₂ - z * L := by
    rw [hγ', show ε₂ * ((1 + L) * γ * (1 - L)) * ε₂ = (ε₂ * (1 + L)) * γ * ((1 - L) * ε₂) by
      simp only [mul_assoc]]
    rw [mul_add, mul_one, hε₂L, add_zero, sub_mul, one_mul, hL2', mul_sub, hzdef]
    congr 1
    rw [show ε₂ * γ * ε₁ * L = ε₂ * γ * (ε₁ * L) by simp only [mul_assoc], hL1']
  -- injectivity of the perturbed block commutator
  have hDinj : ∀ x ∈ W, D x = -(L * z * x + x * z * L) → x = 0 := by
    intro x hx hDx
    obtain ⟨k₀, hk₀⟩ := exists_mem_endFiltration 𝓛 x
    apply eq_zero_of_forall_ge_mem 𝓛 (k₀ := k₀)
    intro m
    induction m with
    | zero => simpa using hk₀
    | succ m ih =>
      have hmem : D x ∈ P ((k₀ + m + 1) - r) := by
        rw [hDx]
        apply neg_mem
        apply add_mem
        · have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hL1 hz) ih
          exact 𝓛.endFiltration_antitone (by omega) h
        · have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration ih hz) hL1
          exact 𝓛.endFiltration_antitone (by omega) h
      have hb := hbound (k₀ + m + 1) (DW ⟨x, hx⟩) hmem
      rw [← he, LinearEquiv.symm_apply_apply] at hb
      push_cast
      simpa [add_assoc] using hb
  -- transfer the field property to the conjugate
  intro hfield
  have hu : (1 + L) * (1 - L) = 1 := by
    rw [mul_sub, mul_one, add_mul, one_mul, hLL, add_zero, add_sub_cancel_right]
  have hu' : (1 - L) * (1 + L) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hLL, add_zero, add_sub_cancel_right]
  let eu : V ≃ₗ[F] V := LinearEquiv.ofLinearMap (1 + L) (1 - L) hu hu'
  let φ : A ≃ₐ[F] A := LinearEquiv.conjAlgEquiv F eu
  have hφ : φ γ = γ' := by
    rw [LinearEquiv.conjAlgEquiv_apply]
    rfl
  have hmap : (elementAlgebra γ).map φ.toAlgHom = elementAlgebra γ' := by
    rw [AlgHom.map_adjoin_singleton]
    change Algebra.adjoin F {φ γ} = _
    rw [hφ]
  have hfield' : IsField (elementAlgebra γ') := by
    rw [← hmap]
    exact ((Subalgebra.equivMapOfInjective (elementAlgebra γ) φ.toAlgHom
      φ.injective).symm.toMulEquiv).isField hfield
  let : Field (elementAlgebra γ') := hfield'.toField
  -- vectors in both blocks
  have hvec : ∀ ε : A, ε * ε = ε → ε ≠ 0 → ∃ w : V, ε w = w ∧ w ≠ 0 := by
    intro ε hεε hε0
    by_contra hcon
    push Not at hcon
    apply hε0
    ext v
    have h := hcon (ε v) (by rw [← Module.End.mul_apply, hεε])
    simpa using h
  obtain ⟨w₁, hw₁, hw₁0⟩ := hvec ε₁ h11 hne₁
  obtain ⟨w₂, hw₂, hw₂0⟩ := hvec ε₂ h22 hne₂
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (elementAlgebra γ') hw₂0
  let ψ : V →ₗ[elementAlgebra γ'] V := f.smulRight w₁
  let ψF : A := ψ.restrictScalars F
  have hψw : ψF w₂ = w₁ := by
    change f w₂ • w₁ = w₁
    rw [hf, one_smul]
  have hcomm : ψF * γ' = γ' * ψF := by
    ext v
    change ψ (γ' v) = γ' (ψ v)
    have hγv : ∀ u : V, γ' u = (⟨γ', Algebra.self_mem_adjoin_singleton F γ'⟩ :
      elementAlgebra γ') • u := fun u => rfl
    rw [hγv, hγv, map_smul]
  -- the intertwiner
  set x := ε₁ * ψF * ε₂ with hxdef
  have hxW : x ∈ W := by
    apply hWmem
    · rw [hxdef, ← mul_assoc, ← mul_assoc, h11]
    · rw [hxdef, mul_assoc, h22]
  have hD' : ε₁ * γ' * ε₁ * x - x * (ε₂ * γ' * ε₂) = 0 := by
    have hε₂γ' : ε₂ * γ' * ε₂ = γ' * ε₂ - ε₁ * γ' * ε₂ := by
      rw [eq_sub_iff_add_eq, ← add_mul, ← add_mul, add_comm, hsum, one_mul]
    have hγ'ε : γ' = ε₁ * γ' + ε₂ * γ' := by rw [← add_mul, hsum, one_mul]
    have h1 : x * (ε₂ * γ' * ε₂) = ε₁ * γ' * ε₁ * ψF * ε₂ := by
      calc x * (ε₂ * γ' * ε₂) = ε₁ * ψF * (ε₂ * ε₂ * γ' * ε₂) := by
            rw [hxdef]; simp only [mul_assoc]
        _ = ε₁ * ψF * (γ' * ε₂) := by
            rw [h22, hε₂γ', hK1, sub_zero]
        _ = ε₁ * (γ' * ψF) * ε₂ := by
            rw [← hcomm]; simp only [mul_assoc]
        _ = ε₁ * γ' * (ε₁ + ε₂) * ψF * ε₂ := by
            rw [hsum, mul_one]; simp only [mul_assoc]
        _ = ε₁ * γ' * ε₁ * ψF * ε₂ + ε₁ * γ' * ε₂ * (ψF * ε₂) := by
            rw [mul_add, add_mul, add_mul]; simp only [mul_assoc]
        _ = ε₁ * γ' * ε₁ * ψF * ε₂ := by
            rw [hK1, zero_mul, add_zero]
    have h2 : ε₁ * γ' * ε₁ * x = ε₁ * γ' * ε₁ * ψF * ε₂ := by
      rw [hxdef, show ε₁ * γ' * ε₁ * (ε₁ * ψF * ε₂) = ε₁ * γ' * (ε₁ * ε₁) * ψF * ε₂ by
        simp only [mul_assoc], h11]
    rw [h1, h2, sub_self]
  have hx0 : x = 0 := by
    apply hDinj x hxW
    have hexp : ε₁ * γ' * ε₁ * x - x * (ε₂ * γ' * ε₂) =
        D x + (L * z * x + x * z * L) := by
      rw [hK2, hK3, hDdef, blockCommutator_apply]
      noncomm_ring
    rw [hD'] at hexp
    rw [eq_neg_iff_add_eq_zero, ← hexp]
  have hxw : x w₂ = w₁ := by
    rw [hxdef, Module.End.mul_apply, Module.End.mul_apply, hw₂, hψw, hw₁]
  apply hw₁0
  rw [← hxw, hx0]
  rfl

end Langlands.BushnellKutzko.SplitObstruction
