import Langlands.GroupScheme.SymplecticInnerForm.SymplecticInvolutionAntihermitian
import Langlands.GroupScheme.OrthogonalMatrix.Basic

/-!
# Orthogonal involutions are adjoint to hermitian division forms

Let `A` be a finite-dimensional central simple `K`-algebra with an involution of the first
kind `τ` which becomes, over some field `L/K`, the adjoint involution `y ↦ J yᵀ J` of the
symmetric matrix `J = [[0, 1], [1, 0]]` (the polar matrix of the split quadratic form).
Writing `A ≅ M_m(D)` (Wedderburn) and the transported involution as `Int(U) ∘ θ*` with
`θ*(U) = ε • U` (the corner construction of `CornerInvolution`), the dimension of the
symmetric elements of `τ`, computed over `L`, forces `dim (θ-ε-symmetric) = d (d + 1) / 2`.
If `ε = -1` (characteristic not two), a nonzero skew element of `θ` changes the sign of the
corner construction to `ε = 1`. Hence `τ` is the adjoint involution of an invertible
`θ`-hermitian matrix, and `θ` is of Tits type 1.
-/

noncomputable section

universe u v w

open scoped TensorProduct
open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

/-! ### The split side -/

section Chart

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]
  (τ : FirstKindInvolution K A) {n : ℕ} {L : Type w} [Field L] [Algebra K L]
  (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L)

theorem map_polarChart_eq
    (he : ∀ x, e (τ.baseChange L x) * OrthogonalMatrix.polarMatrix (Fin n) L =
      OrthogonalMatrix.polarMatrix (Fin n) L * (e x)ᵀ)
    (x : L ⊗[K] A) :
    e (τ.baseChange L x) =
      OrthogonalMatrix.polarMatrix (Fin n) L * (e x)ᵀ * OrthogonalMatrix.polarMatrix (Fin n) L := by
  rw [← he, mul_assoc, OrthogonalMatrix.polarMatrix_mul_self, mul_one]

/-- The identity involution of a field has a one-dimensional space of symmetric elements. -/
theorem finrank_epsSymmetric_one_scalarInvolution (L : Type w) [Field L] :
    Module.finrank L ((Symplectic.scalarInvolution L).epsSymmetric 1) = 1 := by
  have h : (Symplectic.scalarInvolution L).epsSymmetric 1 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_epsSymmetric, Symplectic.scalarInvolution_apply, one_smul]
  rw [h, finrank_top, Module.finrank_self]

/-- If `τ_L` is the adjoint involution of the symmetric polar matrix `J`, the symmetric
elements of `τ` have dimension `2n + (2n choose 2)`. -/
theorem finrank_symmetricSubspace_of_polarChart
    (he : ∀ x, e (τ.baseChange L x) * OrthogonalMatrix.polarMatrix (Fin n) L =
      OrthogonalMatrix.polarMatrix (Fin n) L * (e x)ᵀ) :
    Module.finrank K τ.symmetricSubspace = 2 * n + (2 * n).choose 2 := by
  rw [← τ.finrank_symmetricSubspace_baseChange L]
  have h1 := ((τ.baseChange L).epsSymmetricCongr e 1).finrank_eq
  rw [epsSymmetric_one, epsSymmetric_one] at h1
  have hτ : ∀ y, ((τ.baseChange L).algEquivCongr e) y =
      OrthogonalMatrix.polarMatrix (Fin n) L *
        (Symplectic.scalarInvolution L).matrix (Fin n ⊕ Fin n) y *
          OrthogonalMatrix.polarMatrix (Fin n) L := by
    intro y
    rw [algEquivCongr_apply, map_polarChart_eq τ e he, AlgEquiv.apply_symm_apply,
      Symplectic.scalarInvolution_matrix]
  have hθJ : (Symplectic.scalarInvolution L).matrix (Fin n ⊕ Fin n)
      (OrthogonalMatrix.polarMatrix (Fin n) L) =
      (1 : L) • OrthogonalMatrix.polarMatrix (Fin n) L := by
    rw [Symplectic.scalarInvolution_matrix, OrthogonalMatrix.polarMatrix_transpose, one_smul]
  rw [h1, finrank_symmetricSubspace_eq_of_gram _ _ (by norm_num)
      (OrthogonalMatrix.polarMatrix_mul_self) (OrthogonalMatrix.polarMatrix_mul_self) hθJ hτ,
    finrank_epsSymmetric_matrix _ _ (by norm_num),
    finrank_epsSymmetric_one_scalarInvolution, Module.finrank_self, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, mul_one, mul_one]

end Chart

/-! ### Changing the sign of the corner construction -/

section SignFlip

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Every involution of the first kind of `M_ι(D)` is `Int(U) ∘ θ*` with `θ*(U) = ε • U`;
if `θ` has a nonzero skew element, the corner construction can be redone with the opposite
sign `-ε`. -/
theorem exists_isGramModel_signFlip [Nonempty ι] (τ : FirstKindInvolution K (Matrix ι ι D)) :
    ∃ (θ : FirstKindInvolution K D) (ε : K) (U U' : Matrix ι ι D),
      IsGramModel τ θ ε U U' ∧
        (∀ v : D, v ≠ 0 → θ v = -v →
          ∃ (θ' : FirstKindInvolution K D) (U₂ U₂' : Matrix ι ι D),
            IsGramModel τ θ' (-ε) U₂ U₂') := by
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨x, ε, hx, hx0, hε, hτx⟩ := exists_isCorner_eps τ i₀
  obtain ⟨c, rfl, rfl⟩ := exists_cornerData hx hx0 hε hτx
  refine ⟨c.involution, c.ε, c.gram, c.gramInv, c.isGramModel τ, ?_⟩
  intro v hv hθv
  have hc2 : IsCorner τ i₀ (single i₀ i₀ v * c.w) :=
    ⟨by rw [← mul_assoc, single_mul_single_same, one_mul], by rw [mul_assoc, c.w_mul_f]⟩
  have hc20 : single i₀ i₀ v * c.w ≠ 0 := by
    intro h
    apply c.w_ne_zero
    calc c.w = single i₀ i₀ 1 * c.w := c.single_mul_w.symm
      _ = single i₀ i₀ v⁻¹ * (single i₀ i₀ v * c.w) := by
          rw [← mul_assoc, single_mul_single_same, inv_mul_cancel₀ hv]
      _ = 0 := by rw [h, mul_zero]
  have hτ2 : τ (single i₀ i₀ v * c.w) = (-c.ε) • (single i₀ i₀ v * c.w) := by
    rw [map_mul, c.map_w, smul_mul_assoc, c.w_mul_map_single, hθv, ← single_neg, neg_mul,
      neg_smul, smul_neg]
  obtain ⟨c₂, -, hε₂⟩ := exists_cornerData hc2 hc20
    (by rw [neg_mul_neg]; exact c.ε_mul_self) hτ2
  refine ⟨c₂.involution, c₂.gram, c₂.gramInv, ?_⟩
  rw [← hε₂]
  exact c₂.isGramModel τ

end SignFlip

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.OrthogonalInnerForm

open Quaternionic

/-! ### Arithmetic -/

theorem choose_two_mul (m d : ℕ) :
    (m * d).choose 2 = m * d.choose 2 + m.choose 2 * (d * d) := by
  have h : (((m * d).choose 2 : ℕ) : ℚ) = ((m * d.choose 2 + m.choose 2 * (d * d) : ℕ) : ℚ) := by
    rw [Nat.cast_choose_two]
    push_cast
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
    ring
  exact_mod_cast h

theorem eq_of_finrank_count {m d s N : ℕ} (hm : 0 < m) (hN : m * d = N)
    (h : m * s + m.choose 2 * (d * d) = N + N.choose 2) : s = d + d.choose 2 := by
  subst hN
  rw [choose_two_mul] at h
  apply Nat.eq_of_mul_eq_mul_left hm
  rw [mul_add]
  linarith

theorem mul_succ_div_two (d : ℕ) : d * (d + 1) / 2 = d + d.choose 2 := by
  have h : (d + 1).choose 2 = d + d.choose 2 := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  rw [← h, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

/-! ### The classification -/

/-- **Orthogonal involutions are adjoint involutions of hermitian division forms.**
Let `A` be a finite-dimensional central simple `K`-algebra with an involution of the first
kind `τ`, and suppose an `L`-algebra isomorphism `e : L ⊗[K] A ≃ M_{2n}(L)` carries `τ_L`
to the adjoint involution of the symmetric polar matrix `J = [[0, 1], [1, 0]]`, in the form
`e (τ_L x) * J = J * ᵗ(e x)`. Then there are a central division `K`-algebra `D` of degree
`degree`, with `m * degree = 2 * n`, an involution of the first kind `σ` of `D` whose symmetric
space has dimension `degree * (degree + 1) / 2`, an invertible `σ`-hermitian matrix
`H ∈ M_m(D)` (`ᵗH^σ = H`) and a `K`-algebra isomorphism `φ : A ≃ M_m(D)` with
`φ (τ x) * H = H * ᵗ(φ x)^σ` for every `x`. -/
theorem orthogonalInvolutionHermitian {K A : Type u} [Field K] [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (τ : FirstKindInvolution K A) {n : ℕ} {L : Type u} [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L)
    (he : ∀ x, e (τ.baseChange L x) * OrthogonalMatrix.polarMatrix (Fin n) L =
      OrthogonalMatrix.polarMatrix (Fin n) L * (e x).transpose) :
    ∃ (degree m : ℕ) (_ : NeZero m)
      (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
      0 < degree ∧ m * degree = 2 * n ∧
      Module.finrank K D = degree ^ 2 ∧
        ∃ σ : FirstKindInvolution K D,
          Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 ∧
            ∃ H : Matrix (Fin m) (Fin m) D,
              σ.matrix (Fin m) H = H ∧ IsUnit H ∧
                ∃ φ : A ≃ₐ[K] Matrix (Fin m) (Fin m) D,
                  ∀ x, φ (τ x) * H = H * σ.matrix (Fin m) (φ x) := by
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
  have hSym := τ.finrank_symmetricSubspace_of_polarChart e he
  have hcount : ∀ (θ : FirstKindInvolution K D) (ε : K) (U U' : Matrix (Fin m) (Fin m) D),
      FirstKindInvolution.IsGramModel τB θ ε U U' →
        Module.finrank K (θ.epsSymmetric ε) = d + d.choose 2 := by
    intro θ ε U U' hG
    have h := hG.finrank_symmetricSubspace
    rw [hSymB, hSym, Fintype.card_fin, hD] at h
    exact eq_of_finrank_count hm0 hmd h.symm
  -- a model with sign `1`
  obtain ⟨θ, U, U', hG⟩ : ∃ (θ : FirstKindInvolution K D) (U U' : Matrix (Fin m) (Fin m) D),
      FirstKindInvolution.IsGramModel τB θ 1 U U' := by
    obtain ⟨θ₀, ε, U₀, U₀', hG₀, hflip⟩ := FirstKindInvolution.exists_isGramModel_signFlip τB
    have hε : ε * ε = 1 := hG₀.1
    by_cases h2 : (2 : K) = 0
    · have hε1 : ε = 1 := by
        have h' : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
        exact sub_eq_zero.1 (mul_self_eq_zero.1 h')
      exact ⟨θ₀, U₀, U₀', hε1 ▸ hG₀⟩
    · rcases mul_self_eq_one_iff.1 hε with h1 | h1
      · exact ⟨θ₀, U₀, U₀', h1 ▸ hG₀⟩
      · have hs := hcount θ₀ ε U₀ U₀' hG₀
        rw [h1] at hs
        have hpos : 0 < Module.finrank K (θ₀.epsSymmetric (-1)) := by omega
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
            (p := θ₀.epsSymmetric (-1)) fun h => by
          rw [h, finrank_bot] at hpos
          exact lt_irrefl 0 hpos
        have hθv : θ₀ v = -v := ((θ₀.mem_epsSymmetric).1 hv).trans (neg_one_smul K v)
        obtain ⟨θ', U₂, U₂', hG₂⟩ := hflip v hv0 hθv
        rw [h1, neg_neg] at hG₂
        exact ⟨θ', U₂, U₂', hG₂⟩
  have hs := hcount θ 1 U U' hG
  rw [FirstKindInvolution.epsSymmetric_one] at hs
  obtain ⟨-, hUU', hU'U, hθU, hτU⟩ := hG
  refine ⟨d, m, hm, D, inferInstance, inferInstance, inferInstance, inferInstance, hd, hmd,
    by rw [hD, sq], θ, by rw [hs, mul_succ_div_two], U, by rw [hθU, one_smul],
    ⟨⟨U, U', hUU', hU'U⟩, rfl⟩, φ, fun x => ?_⟩
  have h := hτU (φ x)
  rw [hτB, FirstKindInvolution.algEquivCongr_apply_map] at h
  rw [h, mul_assoc _ U', hU'U, mul_one]

end Langlands.GroupScheme.OrthogonalInnerForm
