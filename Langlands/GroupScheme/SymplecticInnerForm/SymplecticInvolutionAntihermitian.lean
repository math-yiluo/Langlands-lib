import Langlands.GroupScheme.SymplecticInnerForm.CornerInvolution
import Langlands.GroupScheme.SimplyConnected.SymplecticInvolutionAntihermitianStatement
import Langlands.GroupScheme.Symplectic.Basic
import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.Algebra.CentralSimple.SeparablyClosedSplitting
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Symplectic involutions are adjoint to antihermitian division forms

This module proves `Langlands.GroupScheme.SymplecticInvolutionAntihermitianStatement`.
Write the central simple algebra as `A ≅ M_m(D)` (Wedderburn) and the transported involution
as `τ_B = Int(U) ∘ θ*` with `θ*(U) = ε • U` (the corner construction). Comparing the dimension
of the symmetric elements over `K` with the dimension over the splitting field, where `τ`
becomes the adjoint involution of the standard alternating matrix, gives the sign `ε = -1`
(after the sign change of the corner construction when necessary) and the dimension of the
symmetric elements of `θ`. In characteristic two, the identity is alternating for `τ`, which
makes the diagonal entries of `U` alternating for `θ`.
-/

noncomputable section

universe u v w

open scoped TensorProduct
open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

/-! ### Symmetric elements under extension of scalars -/

section BaseChange

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]
  (τ : FirstKindInvolution K A) (L : Type w) [Field L] [Algebra K L]

/-- Extension of scalars preserves the dimension of the symmetric elements. -/
theorem finrank_symmetricSubspace_baseChange :
    Module.finrank L (τ.baseChange L).symmetricSubspace =
      Module.finrank K τ.symmetricSubspace := by
  have h : (τ.baseChange L).toLinearMap - LinearMap.id =
      (τ.toLinearMap - LinearMap.id).baseChange L := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_id]
    rfl
  have h' : (τ.baseChange L).symmetricSubspace =
      LinearMap.ker ((τ.toLinearMap - LinearMap.id).baseChange L) := congrArg LinearMap.ker h
  rw [h']
  exact (LinearMap.tensorKerEquiv L L (τ.toLinearMap - LinearMap.id)).finrank_eq.symm.trans
    Module.finrank_baseChange

end BaseChange

/-! ### The scalar involution -/

private theorem two_eq_zero_iff_of_algebra (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] :
    (2 : L) = 0 ↔ (2 : K) = 0 := by
  have h : algebraMap K L 2 = 2 := map_ofNat _ 2
  rw [← h, map_eq_zero_iff _ (algebraMap K L).injective]

/-- In characteristic two, every scalar is skew for the identity involution. -/
theorem finrank_epsSymmetric_scalarInvolution_of_two_eq_zero (L : Type w) [Field L]
    (h2 : (2 : L) = 0) :
    Module.finrank L ((Symplectic.scalarInvolution L).epsSymmetric (-1)) = 1 := by
  have hneg : (-1 : L) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  have h : (Symplectic.scalarInvolution L).epsSymmetric (-1) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_epsSymmetric, Symplectic.scalarInvolution_apply, hneg, one_smul]
  rw [h, finrank_top, Module.finrank_self]

/-- Away from characteristic two, no nonzero scalar is skew for the identity involution. -/
theorem finrank_epsSymmetric_scalarInvolution_of_two_ne_zero (L : Type w) [Field L]
    (h2 : (2 : L) ≠ 0) :
    Module.finrank L ((Symplectic.scalarInvolution L).epsSymmetric (-1)) = 0 := by
  have h : (Symplectic.scalarInvolution L).epsSymmetric (-1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_epsSymmetric, Symplectic.scalarInvolution_apply, neg_one_smul] at hx
    rw [Submodule.mem_bot]
    have h2x : (2 : L) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.1 h2x).resolve_left h2
  rw [h, finrank_bot]

/-! ### The split side -/

section Chart

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]
  (τ : FirstKindInvolution K A) {n : ℕ} {L : Type w} [Field L] [Algebra K L]
  (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L)

theorem map_chart_eq (he : ∀ x, e (τ.baseChange L x) * J (Fin n) L = J (Fin n) L * (e x)ᵀ)
    (x : L ⊗[K] A) : e (τ.baseChange L x) = J (Fin n) L * (e x)ᵀ * -J (Fin n) L := by
  rw [← he, mul_assoc, mul_neg, J_squared, neg_neg, mul_one]

/-- If `τ_L` is the adjoint involution of `J`, the symmetric elements of `τ` have dimension
`2n · s₀ + (2n choose 2)`, where `s₀` is the dimension of the skew scalars of `L` (`1` in
characteristic two and `0` otherwise). -/
theorem finrank_symmetricSubspace_of_chart
    (he : ∀ x, e (τ.baseChange L x) * J (Fin n) L = J (Fin n) L * (e x)ᵀ) :
    Module.finrank K τ.symmetricSubspace =
      2 * n * Module.finrank L ((Symplectic.scalarInvolution L).epsSymmetric (-1)) +
        (2 * n).choose 2 := by
  rw [← τ.finrank_symmetricSubspace_baseChange L]
  have h1 := ((τ.baseChange L).epsSymmetricCongr e 1).finrank_eq
  rw [epsSymmetric_one, epsSymmetric_one] at h1
  have hτ : ∀ y, ((τ.baseChange L).algEquivCongr e) y =
      J (Fin n) L * (Symplectic.scalarInvolution L).matrix (Fin n ⊕ Fin n) y * -J (Fin n) L := by
    intro y
    rw [algEquivCongr_apply, map_chart_eq τ e he, AlgEquiv.apply_symm_apply,
      Symplectic.scalarInvolution_matrix]
  have hθJ : (Symplectic.scalarInvolution L).matrix (Fin n ⊕ Fin n) (J (Fin n) L) =
      (-1 : L) • J (Fin n) L := by
    rw [Symplectic.scalarInvolution_matrix, J_transpose, neg_one_smul]
  rw [h1, finrank_symmetricSubspace_eq_of_gram _ _ (by norm_num)
      (by rw [mul_neg, J_squared, neg_neg]) (by rw [neg_mul, J_squared, neg_neg]) hθJ hτ,
    finrank_epsSymmetric_matrix _ _ (by norm_num),
    Module.finrank_self, Fintype.card_sum, Fintype.card_fin, ← two_mul, mul_one]

/-- In characteristic two, if `τ_L` is the adjoint involution of `J`, then `1` is alternating
for `τ`. -/
theorem one_mem_alternatingSubspace_of_chart (h2 : (2 : K) = 0)
    (he : ∀ x, e (τ.baseChange L x) * J (Fin n) L = J (Fin n) L * (e x)ᵀ) :
    (1 : A) ∈ τ.alternatingSubspace := by
  by_contra h1
  obtain ⟨g, hg1, hle⟩ := Submodule.exists_le_ker_of_notMem h1
  have hg : ∀ a, g (a - τ a) = 0 := fun a => hle (τ.sub_mem_alternatingSubspace a)
  let G : L ⊗[K] A →ₗ[L] L := ((Algebra.linearMap K L) ∘ₗ g).liftBaseChange L
  have hG : ∀ z, G (z - τ.baseChange L z) = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c a =>
      rw [baseChange_tmul, ← TensorProduct.tmul_sub, LinearMap.liftBaseChange_tmul,
        LinearMap.comp_apply, hg, _root_.map_zero, smul_zero]
    | add z z' hz hz' =>
      rw [map_add, add_sub_add_comm, _root_.map_add, hz, hz', add_zero]
  have hneg : (-1 : L) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, (two_eq_zero_iff_of_algebra K L).2 h2]
  let y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L := fromBlocks 1 0 0 0
  have hy : e.symm y - τ.baseChange L (e.symm y) = 1 := by
    apply e.injective
    rw [_root_.map_sub, map_chart_eq τ e he, AlgEquiv.apply_symm_apply, _root_.map_one]
    simp only [y, J, fromBlocks_transpose, fromBlocks_neg, fromBlocks_multiply, transpose_one,
      transpose_zero, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, add_zero, neg_zero,
      neg_neg]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases hij : i = j <;>
      simp [Matrix.one_apply, hij, hneg]
  have h1G := hG (e.symm y)
  rw [hy, Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_one_tmul,
    LinearMap.comp_apply, Algebra.linearMap_apply] at h1G
  exact hg1 ((map_eq_zero_iff _ (algebraMap K L).injective).1 h1G)

end Chart

/-! ### The division-algebra side -/

section Model

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- For `τ = Int(U) ∘ θ*` with `θ*(U) = ε • U`, the symmetric elements of `τ` have dimension
`card ι · dim (θ-ε-symmetric) + (card ι choose 2) · dim D`. -/
theorem IsGramModel.finrank_symmetricSubspace {τ : FirstKindInvolution K (Matrix ι ι D)}
    {θ : FirstKindInvolution K D} {ε : K} {U U' : Matrix ι ι D} (h : IsGramModel τ θ ε U U') :
    Module.finrank K τ.symmetricSubspace =
      Fintype.card ι * Module.finrank K (θ.epsSymmetric ε) +
        (Fintype.card ι).choose 2 * Module.finrank K D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [(θ.matrix ι).finrank_symmetricSubspace_eq_of_gram τ h1 h2 h3 h4 h5,
    θ.finrank_epsSymmetric_matrix ι h1]

end Model

/-! ### Arithmetic -/

private theorem choose_two_mul (m d : ℕ) :
    (m * d).choose 2 = m * d.choose 2 + m.choose 2 * (d * d) := by
  have h : (((m * d).choose 2 : ℕ) : ℚ) = ((m * d.choose 2 + m.choose 2 * (d * d) : ℕ) : ℚ) := by
    rw [Nat.cast_choose_two]
    push_cast
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
    ring
  exact_mod_cast h

private theorem eq_of_finrank_count {m d s t N : ℕ} (hm : 0 < m) (hN : m * d = N)
    (h : m * s + m.choose 2 * (d * d) = N * t + N.choose 2) : s = d * t + d.choose 2 := by
  subst hN
  rw [choose_two_mul] at h
  apply Nat.eq_of_mul_eq_mul_left hm
  rw [mul_add, ← mul_assoc]
  linarith

private theorem mul_succ_div_two (d : ℕ) : d * (d + 1) / 2 = d + d.choose 2 := by
  have h : (d + 1).choose 2 = d + d.choose 2 := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  rw [← h, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

private theorem mul_self_eq_add_two_mul_choose (d : ℕ) : d * d = d + 2 * d.choose 2 := by
  have h : ((d * d : ℕ) : ℚ) = ((d + 2 * d.choose 2 : ℕ) : ℚ) := by
    push_cast
    rw [Nat.cast_choose_two]
    ring
  exact_mod_cast h

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme

open Quaternionic

/-- Symplectic involutions of central simple algebras are adjoint involutions of invertible
trace-valued antihermitian matrices over an involutive central division algebra. -/
theorem symplecticInvolutionAntihermitian : SymplecticInvolutionAntihermitianStatement.{u} := by
  intro K A _ _ _ _ _ _ τ n L _ _ e he
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨m, hm, D, _, _, _, ⟨φ⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have : Algebra.IsCentral K D := CentralSimple.isCentral_of_algEquiv_matrix φ
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have : Nonempty (Fin m) := ⟨⟨0, hm0⟩⟩
  set d := CentralSimple.reducedDegree K D with hd_def
  have hD : Module.finrank K D = d * d := CentralSimple.finrank_eq_reducedDegree_mul_self K D
  have hd : 0 < d := CentralSimple.reducedDegree_pos K D
  -- `m * d = 2 * n`
  have hA1 : Module.finrank K A = (2 * n) * (2 * n) := by
    rw [← Module.finrank_baseChange (R := L), e.toLinearEquiv.finrank_eq,
      Module.finrank_matrix, Module.finrank_self, Fintype.card_sum, Fintype.card_fin]
    ring
  have hA2 : Module.finrank K A = (m * d) * (m * d) := by
    rw [φ.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin, hD]
    ring
  have hmd : m * d = 2 * n := Nat.mul_self_inj.1 (hA2.symm.trans hA1)
  -- the transported involution and the dimension of its symmetric elements
  set τB := τ.algEquivCongr φ with hτB
  have hSymB : Module.finrank K τB.symmetricSubspace = Module.finrank K τ.symmetricSubspace := by
    have h := (τ.epsSymmetricCongr φ 1).finrank_eq
    rw [FirstKindInvolution.epsSymmetric_one, FirstKindInvolution.epsSymmetric_one] at h
    exact h.symm
  have hSym := τ.finrank_symmetricSubspace_of_chart e he
  set t : ℕ := Module.finrank L ((Symplectic.scalarInvolution L).epsSymmetric (-1)) with ht
  have hcount : ∀ (θ : FirstKindInvolution K D) (ε : K) (U U' : Matrix (Fin m) (Fin m) D),
      FirstKindInvolution.IsGramModel τB θ ε U U' →
        Module.finrank K (θ.epsSymmetric ε) = d * t + d.choose 2 := by
    intro θ ε U U' hG
    have h := hG.finrank_symmetricSubspace
    rw [hSymB, hSym, Fintype.card_fin, hD] at h
    exact FirstKindInvolution.eq_of_finrank_count hm0 hmd h.symm
  -- a model with sign `-1`
  obtain ⟨θ, U, U', hG⟩ : ∃ (θ : FirstKindInvolution K D) (U U' : Matrix (Fin m) (Fin m) D),
      FirstKindInvolution.IsGramModel τB θ (-1) U U' := by
    obtain ⟨θ₀, ε, U₀, U₀', hG₀, hflip⟩ := FirstKindInvolution.exists_isGramModel τB
    have hε : ε * ε = 1 := hG₀.1
    by_cases h2 : (2 : K) = 0
    · have hε1 : ε = -1 := by
        have h' : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
        have h1 : ε = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 h')
        rw [h1, eq_comm, neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
      exact ⟨θ₀, U₀, U₀', hε1 ▸ hG₀⟩
    · rcases mul_self_eq_one_iff.1 hε with h1 | h1
      · have hs := hcount θ₀ ε U₀ U₀' hG₀
        have ht0 : t = 0 :=
          FirstKindInvolution.finrank_epsSymmetric_scalarInvolution_of_two_ne_zero L fun h =>
            h2 ((FirstKindInvolution.two_eq_zero_iff_of_algebra K L).1 h)
        rw [h1, FirstKindInvolution.epsSymmetric_one, ht0, mul_zero, zero_add] at hs
        have hsum := θ₀.finrank_symmetricSubspace_add_finrank_skew h2
        rw [hs, hD] at hsum
        have hsq := FirstKindInvolution.mul_self_eq_add_two_mul_choose d
        have hpos : 0 < Module.finrank K (θ₀.epsSymmetric (-1)) := by omega
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
            (p := θ₀.epsSymmetric (-1)) fun h => by
          rw [h, finrank_bot] at hpos
          exact lt_irrefl 0 hpos
        have hθv : θ₀ v = -v := ((θ₀.mem_epsSymmetric).1 hv).trans (neg_one_smul K v)
        obtain ⟨θ', U₂, U₂', hG₂⟩ := hflip h1 v hv0 hθv
        exact ⟨θ', U₂, U₂', hG₂⟩
      · exact ⟨θ₀, U₀, U₀', h1 ▸ hG₀⟩
  have hs := hcount θ (-1) U U' hG
  obtain ⟨-, hUU', hU'U, hθU, hτU⟩ := hG
  -- the dimension of the symmetric elements of `θ`
  have hSymθ : Module.finrank K θ.symmetricSubspace = d * (d + 1) / 2 := by
    rw [FirstKindInvolution.mul_succ_div_two]
    by_cases h2 : (2 : K) = 0
    · have hneg : (-1 : K) = 1 := by rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
      have ht1 : t = 1 :=
        FirstKindInvolution.finrank_epsSymmetric_scalarInvolution_of_two_eq_zero L
          ((FirstKindInvolution.two_eq_zero_iff_of_algebra K L).2 h2)
      rw [show θ.symmetricSubspace = θ.epsSymmetric (-1) by
        rw [hneg, FirstKindInvolution.epsSymmetric_one], hs, ht1, mul_one]
    · have ht0 : t = 0 :=
        FirstKindInvolution.finrank_epsSymmetric_scalarInvolution_of_two_ne_zero L fun h =>
          h2 ((FirstKindInvolution.two_eq_zero_iff_of_algebra K L).1 h)
      have hsum := θ.finrank_symmetricSubspace_add_finrank_skew h2
      rw [hs, ht0, mul_zero, zero_add, hD] at hsum
      have hsq := FirstKindInvolution.mul_self_eq_add_two_mul_choose d
      omega
  -- the Gram matrix is antihermitian and trace-valued
  have hanti : θ.IsAntihermitian U := by
    refine ⟨by rw [hθU, neg_one_smul], fun i => ?_⟩
    by_cases h2 : (2 : K) = 0
    · obtain ⟨a, ha⟩ := τ.mem_alternatingSubspace.1
        (τ.one_mem_alternatingSubspace_of_chart e h2 he)
      have hz : φ a - τB (φ a) = 1 := by
        rw [hτB, FirstKindInvolution.algEquivCongr_apply_map, ← _root_.map_sub, ha,
          _root_.map_one]
      have hw : U = φ a * U + θ.matrix (Fin m) (φ a * U) := by
        rw [FirstKindInvolution.map_mul, hθU, neg_one_smul, neg_mul, ← sub_eq_add_neg]
        calc U = (φ a - τB (φ a)) * U := by rw [hz, one_mul]
          _ = φ a * U - U * θ.matrix (Fin m) (φ a) := by
            rw [sub_mul, hτU (φ a), mul_assoc _ U', hU'U, mul_one]
      have hii : U i i = (φ a * U) i i + θ ((φ a * U) i i) := by
        conv_lhs => rw [hw]
        rw [Matrix.add_apply, FirstKindInvolution.matrix_apply]
      have h2D : (2 : D) = 0 := by
        have h : algebraMap K D 2 = 2 := map_ofNat _ 2
        rw [← h, h2, _root_.map_zero]
      have hθθ : θ ((φ a * U) i i) + θ ((φ a * U) i i) = 0 := by
        rw [← two_mul, h2D, zero_mul]
      rw [hii, show (φ a * U) i i + θ ((φ a * U) i i) = (φ a * U) i i - θ ((φ a * U) i i) by
        rw [eq_sub_iff_add_eq, add_assoc, hθθ, add_zero]]
      exact θ.sub_mem_alternatingSubspace _
    · have hii : θ (U i i) = -U i i := by
        have h := congrFun (congrFun hθU i) i
        rwa [FirstKindInvolution.matrix_apply, Matrix.smul_apply, neg_one_smul] at h
      refine θ.mem_alternatingSubspace.2 ⟨(2 : K)⁻¹ • U i i, ?_⟩
      rw [FirstKindInvolution.map_smul, hii, smul_neg, sub_neg_eq_add, ← two_smul K,
        smul_smul, mul_inv_cancel₀ h2, one_smul]
  refine ⟨d, m, hm, D, inferInstance, inferInstance, inferInstance, inferInstance, hd, hmd,
    by rw [hD, sq], θ, hSymθ, U, hanti, ⟨⟨U, U', hUU', hU'U⟩, rfl⟩, φ, fun x => ?_⟩
  have h := hτU (φ x)
  rw [hτB, FirstKindInvolution.algEquivCongr_apply_map] at h
  rw [h, mul_assoc _ U', hU'U, mul_one]

end Langlands.GroupScheme
