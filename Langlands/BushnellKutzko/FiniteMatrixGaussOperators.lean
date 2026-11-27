import Langlands.BushnellKutzko.FiniteMatrixGaussInjectivityStatement
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block

/-! # Injectivity of the finite matrix Gauss operator

For a finite field `k`, a nontrivial additive character `ψ` of `k` and a complex representation
`ρ` of `GL_ι(k)`, the operator `T(v) = ∑_g ψ(tr g) ρ(g) v` is injective
(`FiniteGauss.gaussOp_injective_of_card`). The proof is the elementary rank induction recorded with the
statement: with `S_A(v) = ∑_g ψ(tr(A g)) ρ(g) v`, additive Fourier inversion on the matrix space
recovers `v` from the vectors `S_A(v)`, and every `S_A` vanishes on `ker T`.
-/

noncomputable section

namespace Langlands.BushnellKutzko

open Matrix
open scoped MatrixGroups

universe uK uV

namespace FiniteGauss

variable {k : Type uK} [Field k] [Fintype k] (ψ : AddChar k ℂ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-! ### Additive orthogonality on matrix spaces -/

section Orthogonality

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- For a nonzero matrix `B`, the sum of `ψ(tr(X B))` over all matrices `X` vanishes. -/
theorem sum_addChar_trace_mul_eq_zero (hψ : ψ ≠ 1) {B : Matrix n m k} (hB : B ≠ 0) :
    ∑ X : Matrix m n k, ψ (X * B).trace = 0 := by
  obtain ⟨a, b, hab⟩ : ∃ a b, B a b ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hB (Matrix.ext h)
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  let f : Matrix m n k →+ k :=
    { toFun := fun X => (X * B).trace
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.add_mul, Matrix.trace_add] }
  have hχ : ψ.compAddMonoidHom f ≠ 1 := by
    intro h
    apply hx
    have h' := DFunLike.congr_fun h (Matrix.single b a (x * (B a b)⁻¹))
    rw [AddChar.compAddMonoidHom_apply, AddChar.one_apply] at h'
    change ψ (Matrix.single b a (x * (B a b)⁻¹) * B).trace = 1 at h'
    rwa [Matrix.trace_single_mul, smul_eq_mul, inv_mul_cancel_right₀ hab] at h'
  exact AddChar.sum_eq_zero_of_ne_one hχ

/-- The sum of `ψ(tr(X B))` over all matrices `X` is the number of matrices if `B = 0`, and
zero otherwise. -/
theorem sum_addChar_trace_mul [DecidableEq k] (hψ : ψ ≠ 1) (B : Matrix n m k) :
    ∑ X : Matrix m n k, ψ (X * B).trace =
      if B = 0 then (Fintype.card (Matrix m n k) : ℂ) else 0 := by
  split_ifs with hB
  · subst hB
    simp
  · exact sum_addChar_trace_mul_eq_zero ψ hψ hB

end Orthogonality

/-! ### The operators `S_A` and `T` -/

section General

variable [DecidableEq k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `S_A = ∑_g ψ(tr(A g)) ρ(g)` for a matrix `A`. -/
def twistedGaussOp (A : Matrix ι ι k) (ρ : Representation ℂ (GL ι k) V) : V →ₗ[ℂ] V :=
  ∑ g : GL ι k, ψ (A * g.val).trace • ρ g

/-- The Gauss operator `T = ∑_g ψ(tr g) ρ(g)`. -/
def gaussOp (ρ : Representation ℂ (GL ι k) V) : V →ₗ[ℂ] V :=
  ∑ g : GL ι k, ψ g.val.trace • ρ g

theorem twistedGaussOp_apply (A : Matrix ι ι k) (ρ : Representation ℂ (GL ι k) V) (v : V) :
    twistedGaussOp ψ A ρ v = ∑ g : GL ι k, ψ (A * g.val).trace • ρ g v := by
  simp [twistedGaussOp]

theorem gaussOp_apply (ρ : Representation ℂ (GL ι k) V) (v : V) :
    gaussOp ψ ρ v = ∑ g : GL ι k, ψ g.val.trace • ρ g v := by
  simp [gaussOp]

theorem twistedGaussOp_one (ρ : Representation ℂ (GL ι k) V) :
    twistedGaussOp ψ 1 ρ = gaussOp ψ ρ := by
  simp [twistedGaussOp, gaussOp]

/-- Additive Fourier inversion: `∑_A ψ(-tr A) S_A(v) = |M_ι(k)| v`. -/
theorem sum_twistedGaussOp (hψ : ψ ≠ 1) (ρ : Representation ℂ (GL ι k) V) (v : V) :
    ∑ A : Matrix ι ι k, ψ (-A.trace) • twistedGaussOp ψ A ρ v =
      (Fintype.card (Matrix ι ι k) : ℂ) • v := by
  simp only [twistedGaussOp_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have key (g : GL ι k) : ∑ A : Matrix ι ι k, ψ (-A.trace) * ψ (A * g.val).trace =
      if g = 1 then (Fintype.card (Matrix ι ι k) : ℂ) else 0 := by
    have h1 (A : Matrix ι ι k) :
        ψ (-A.trace) * ψ (A * g.val).trace = ψ (A * (g.val - 1)).trace := by
      rw [← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
        neg_add_eq_sub]
    simp_rw [h1, sum_addChar_trace_mul ψ hψ]
    by_cases hg : g = 1
    · rw [ite_eq_left (by rw [hg, Units.val_one, sub_self]), ite_eq_left hg]
    · refine (ite_eq_right fun h => hg (Units.ext ?_)).trans (ite_eq_right hg).symm
      rw [Units.val_one]
      exact sub_eq_zero.mp h
  simp_rw [← Finset.sum_smul, key, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, map_one, Module.End.one_apply]

/-- Right multiplication: `S_{A h} = ρ(h)⁻¹ S_A`. -/
theorem twistedGaussOp_mul (A : Matrix ι ι k) (h : GL ι k) (ρ : Representation ℂ (GL ι k) V)
    (v : V) : twistedGaussOp ψ (A * h.val) ρ v = ρ h⁻¹ (twistedGaussOp ψ A ρ v) := by
  simp only [twistedGaussOp_apply, map_sum, map_smul]
  symm
  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Equiv.coe_mulLeft, Units.val_mul, Matrix.mul_assoc, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel_left]

/-- The Gauss operator commutes with the action. -/
theorem gaussOp_map (ρ : Representation ℂ (GL ι k) V) (h : GL ι k) (v : V) :
    gaussOp ψ ρ (ρ h v) = ρ h (gaussOp ψ ρ v) := by
  simp only [gaussOp_apply, map_sum, map_smul]
  rw [← Equiv.sum_comp (MulAut.conj h).toEquiv]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, Units.val_mul,
    Matrix.trace_units_conj]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The Gauss operator commutes with every `S_A`. -/
theorem gaussOp_twistedGaussOp (A : Matrix ι ι k) (ρ : Representation ℂ (GL ι k) V) (v : V) :
    gaussOp ψ ρ (twistedGaussOp ψ A ρ v) = twistedGaussOp ψ A ρ (gaussOp ψ ρ v) := by
  rw [twistedGaussOp_apply, twistedGaussOp_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, gaussOp_map]

/-- If `A u = A`, then `S_A(v)` is fixed by `u`. -/
theorem twistedGaussOp_fixed (A : Matrix ι ι k) (u : GL ι k) (hu : A * u.val = A)
    (ρ : Representation ℂ (GL ι k) V) (v : V) :
    ρ u (twistedGaussOp ψ A ρ v) = twistedGaussOp ψ A ρ v := by
  have h1 : A * (u⁻¹ : GL ι k).val = A := by
    calc A * (u⁻¹ : GL ι k).val = (A * u.val) * (u⁻¹ : GL ι k).val := by rw [hu]
      _ = A := by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
  have h2 := twistedGaussOp_mul ψ A u⁻¹ ρ v
  rw [h1, inv_inv] at h2
  exact h2.symm

/-- **Criterion.** If every `S_A` with `A` singular vanishes on `ker T`, then `T` is
injective. -/
theorem gaussOp_injective_of_singular (hψ : ψ ≠ 1) (ρ : Representation ℂ (GL ι k) V)
    (h : ∀ v, gaussOp ψ ρ v = 0 → ∀ A : Matrix ι ι k, A.det = 0 →
      twistedGaussOp ψ A ρ v = 0) :
    Function.Injective (gaussOp ψ ρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hS (A : Matrix ι ι k) : twistedGaussOp ψ A ρ v = 0 := by
    by_cases hA : A.det = 0
    · exact h v hv A hA
    · let g := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
      have hg : A = (1 : Matrix ι ι k) * g.val := by
        rw [Matrix.one_mul]
        rfl
      rw [hg, twistedGaussOp_mul, twistedGaussOp_one, hv, map_zero]
  have h2 := sum_twistedGaussOp ψ hψ ρ v
  simp only [hS, smul_zero, Finset.sum_const_zero] at h2
  have hc : (Fintype.card (Matrix ι ι k) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (smul_eq_zero.mp h2.symm).resolve_left hc

end General

/-! ### Change of index type -/

section Reindex

variable [DecidableEq k] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- `GL_ι(k) ≃ GL_ι'(k)` induced by an equivalence of index types. -/
def glReindex (e : ι ≃ ι') : GL ι k ≃* GL ι' k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

omit [Fintype k] [DecidableEq k] in
theorem glReindex_val (e : ι ≃ ι') (g : GL ι k) :
    (glReindex e g).val = Matrix.reindex e e g.val :=
  rfl

omit [Fintype k] [DecidableEq k] [DecidableEq ι] [DecidableEq ι'] in
theorem trace_reindex_self (e : ι ≃ ι') (M : Matrix ι ι k) :
    (Matrix.reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp fun i => M i i

theorem gaussOp_comp_glReindex (e : ι ≃ ι') (ρ : Representation ℂ (GL ι' k) V) (v : V) :
    gaussOp ψ (ρ.comp (glReindex e).toMonoidHom) v = gaussOp ψ ρ v := by
  rw [gaussOp_apply, gaussOp_apply, ← Equiv.sum_comp (glReindex (k := k) e).toEquiv]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, glReindex_val, trace_reindex_self]

end Reindex

/-! ### Block matrices and the parabolic averaging -/

section Block

variable [DecidableEq k] {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
  [DecidableEq ι₂]

omit [Fintype k] [DecidableEq k] [DecidableEq ι₁] [DecidableEq ι₂] in
theorem trace_fromBlocks (A : Matrix ι₁ ι₁ k) (B : Matrix ι₁ ι₂ k) (C : Matrix ι₂ ι₁ k)
    (D : Matrix ι₂ ι₂ k) : (fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- The block-diagonal embedding `GL_{ι₁}(k) × GL_{ι₂}(k) → GL_{ι₁ ⊕ ι₂}(k)`,
`(a, D) ↦ diag(a, D)`. -/
def blockDiagHom : GL ι₁ k × GL ι₂ k →* GL (ι₁ ⊕ ι₂) k where
  toFun p := ⟨fromBlocks p.1.val 0 0 p.2.val,
    fromBlocks (p.1⁻¹ : GL ι₁ k).val 0 0 (p.2⁻¹ : GL ι₂ k).val,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  map_one' := Units.ext (by simp)
  map_mul' p q := Units.ext (by simp [fromBlocks_multiply])

omit [Fintype k] [DecidableEq k] in
theorem blockDiagHom_val (p : GL ι₁ k × GL ι₂ k) :
    (blockDiagHom p).val = fromBlocks p.1.val 0 0 p.2.val :=
  rfl

/-- The unipotent element `u(X) = [1 X; 0 1]` of `GL_{ι₁ ⊕ ι₂}(k)`. -/
def blockUnipotent (X : Matrix ι₁ ι₂ k) : GL (ι₁ ⊕ ι₂) k :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

omit [Fintype k] [DecidableEq k] in
theorem blockUnipotent_val (X : Matrix ι₁ ι₂ k) :
    (blockUnipotent X).val = fromBlocks 1 X 0 1 :=
  rfl

omit [Fintype k] [DecidableEq k] in
/-- `tr(M u(X)) = tr M + tr(X C)`, with `C` the lower left block of `M`. -/
theorem trace_mul_fromBlocks_unipotent (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k)
    (X : Matrix ι₁ ι₂ k) :
    (M * fromBlocks 1 X 0 1).trace = M.trace + (X * M.toBlocks₂₁).trace := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, M = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks M).symm⟩
  simp only [fromBlocks_multiply, trace_fromBlocks, toBlocks_fromBlocks₂₁, Matrix.mul_one,
    Matrix.mul_zero, add_zero, Matrix.trace_add, Matrix.trace_mul_comm C X]
  ring

omit [Fintype k] [DecidableEq k] in
theorem blockDiagHom_mul_blockUnipotent_val (a : GL ι₁ k) (D : GL ι₂ k) (X : Matrix ι₁ ι₂ k) :
    (blockDiagHom (a, D) * blockUnipotent X).val = fromBlocks a.val (a.val * X) 0 D.val := by
  rw [Units.val_mul, blockDiagHom_val, blockUnipotent_val, fromBlocks_multiply]
  simp

omit [Fintype k] [DecidableEq k] in
theorem val_mk'' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n k) (h : IsUnit A.det) :
    (Matrix.GeneralLinearGroup.mk'' A h).val = A :=
  rfl

omit [Fintype k] [DecidableEq k] in
theorem isUnit_det_toBlocks (g : GL (ι₁ ⊕ ι₂) k) (hg : g.val.toBlocks₂₁ = 0) :
    IsUnit g.val.toBlocks₁₁.det ∧ IsUnit g.val.toBlocks₂₂.det := by
  have hdet : g.val.det = g.val.toBlocks₁₁.det * g.val.toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks g.val, hg]
    exact det_fromBlocks_zero₂₁ _ _ _
  have hu := Matrix.isUnits_det_units g
  rw [hdet] at hu
  exact ⟨isUnit_of_mul_isUnit_left hu, isUnit_of_mul_isUnit_right hu⟩

/-- The factorization `g = diag(a, D) u(X)` of a matrix with zero lower left block, as the
triple `(a, D, X)`. -/
def lowerBlockZeroFactor (g : GL (ι₁ ⊕ ι₂) k) (hg : g.val.toBlocks₂₁ = 0) :
    GL ι₁ k × GL ι₂ k × Matrix ι₁ ι₂ k :=
  (Matrix.GeneralLinearGroup.mk'' g.val.toBlocks₁₁ (isUnit_det_toBlocks g hg).1,
    Matrix.GeneralLinearGroup.mk'' g.val.toBlocks₂₂ (isUnit_det_toBlocks g hg).2,
    ((Matrix.GeneralLinearGroup.mk'' g.val.toBlocks₁₁ (isUnit_det_toBlocks g hg).1)⁻¹ :
      GL ι₁ k).val * g.val.toBlocks₁₂)

/-- Summing over the matrices with zero lower left block is summing over the triples
`(a, D, X)` through `(a, D, X) ↦ diag(a, D) u(X)`. -/
theorem sum_lowerBlockZero {M : Type*} [AddCommMonoid M] (F : GL (ι₁ ⊕ ι₂) k → M) :
    ∑ g ∈ Finset.univ.filter (fun g : GL (ι₁ ⊕ ι₂) k => g.val.toBlocks₂₁ = 0), F g =
      ∑ t : GL ι₁ k × GL ι₂ k × Matrix ι₁ ι₂ k,
        F (blockDiagHom (t.1, t.2.1) * blockUnipotent t.2.2) := by
  symm
  refine Finset.sum_bij' (fun t _ => blockDiagHom (t.1, t.2.1) * blockUnipotent t.2.2)
    (fun g hg => lowerBlockZeroFactor g (Finset.mem_filter.mp hg).2) ?_ ?_ ?_ ?_ ?_
  · intro t _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [blockDiagHom_mul_blockUnipotent_val, toBlocks_fromBlocks₂₁]
  · intro g _
    exact Finset.mem_univ _
  · rintro ⟨a, D, X⟩ -
    have hval := blockDiagHom_mul_blockUnipotent_val a D X
    simp only [lowerBlockZeroFactor]
    refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_)
    · rw [val_mk'', hval, toBlocks_fromBlocks₁₁]
    · rw [val_mk'', hval, toBlocks_fromBlocks₂₂]
    · dsimp only
      have ha : Matrix.GeneralLinearGroup.mk''
          (blockDiagHom (a, D) * blockUnipotent X).val.toBlocks₁₁
          (isUnit_det_toBlocks _ (by rw [hval, toBlocks_fromBlocks₂₁])).1 = a :=
        Units.ext (by rw [val_mk'', hval, toBlocks_fromBlocks₁₁])
      rw [ha, hval, toBlocks_fromBlocks₁₂, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
  · intro g hg
    have hg' := (Finset.mem_filter.mp hg).2
    apply Units.ext
    simp only [lowerBlockZeroFactor]
    rw [blockDiagHom_mul_blockUnipotent_val, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
    change fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂ 0 g.val.toBlocks₂₂ = g.val
    rw [← hg', fromBlocks_toBlocks]
  · intro t _
    rfl

/-- **No `U`-fixed vectors in the kernel.** If the Gauss operators of `GL_{ι₁}(k)` and
`GL_{ι₂}(k)` are injective on every representation, then the kernel of the Gauss operator of a
representation of `GL_{ι₁ ⊕ ι₂}(k)` contains no nonzero vector fixed by all `u(X)`. -/
theorem eq_zero_of_blockUnipotent_fixed (hψ : ψ ≠ 1)
    (h₁ : ∀ ρ : Representation ℂ (GL ι₁ k) V, Function.Injective (gaussOp ψ ρ))
    (h₂ : ∀ ρ : Representation ℂ (GL ι₂ k) V, Function.Injective (gaussOp ψ ρ))
    (ρ : Representation ℂ (GL (ι₁ ⊕ ι₂) k) V) (v : V) (hv : gaussOp ψ ρ v = 0)
    (hfix : ∀ X, ρ (blockUnipotent X) v = v) : v = 0 := by
  have hN : (Fintype.card (Matrix ι₁ ι₂ k) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set N : ℂ := (Fintype.card (Matrix ι₁ ι₂ k) : ℂ) with hN_def
  let d : GL ι₁ k →* GL (ι₁ ⊕ ι₂) k := blockDiagHom.comp (MonoidHom.inl _ _)
  let e : GL ι₂ k →* GL (ι₁ ⊕ ι₂) k := blockDiagHom.comp (MonoidHom.inr _ _)
  have h1 : N • gaussOp ψ ρ v = ∑ g : GL (ι₁ ⊕ ι₂) k,
      (if g.val.toBlocks₂₁ = 0 then N else 0) • ψ g.val.trace • ρ g v := by
    have hX (X : Matrix ι₁ ι₂ k) : gaussOp ψ ρ v =
        ∑ g : GL (ι₁ ⊕ ι₂) k, (ψ g.val.trace * ψ (X * g.val.toBlocks₂₁).trace) • ρ g v := by
      rw [gaussOp_apply, ← Equiv.sum_comp (Equiv.mulRight (blockUnipotent X))]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Equiv.coe_mulRight]
      rw [map_mul, Module.End.mul_apply, hfix, Units.val_mul, blockUnipotent_val,
        trace_mul_fromBlocks_unipotent, AddChar.map_add_eq_mul]
    calc N • gaussOp ψ ρ v = ∑ _X : Matrix ι₁ ι₂ k, gaussOp ψ ρ v := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
      _ = ∑ X : Matrix ι₁ ι₂ k, ∑ g : GL (ι₁ ⊕ ι₂) k,
            (ψ g.val.trace * ψ (X * g.val.toBlocks₂₁).trace) • ρ g v :=
          Finset.sum_congr rfl fun X _ => hX X
      _ = ∑ g : GL (ι₁ ⊕ ι₂) k, (∑ X : Matrix ι₁ ι₂ k, ψ (X * g.val.toBlocks₂₁).trace) •
            ψ g.val.trace • ρ g v := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun X _ => ?_
          rw [smul_smul, mul_comm]
      _ = _ := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [sum_addChar_trace_mul ψ hψ]
  have hΦ (a : GL ι₁ k) (D : GL ι₂ k) (X : Matrix ι₁ ι₂ k) :
      ψ (blockDiagHom (a, D) * blockUnipotent X).val.trace •
          ρ (blockDiagHom (a, D) * blockUnipotent X) v =
        ψ a.val.trace • ψ D.val.trace • ρ (d a) (ρ (e D) v) := by
    have hde : blockDiagHom (a, D) = d a * e D := by
      simp only [d, e, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
        MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [blockDiagHom_mul_blockUnipotent_val, trace_fromBlocks, AddChar.map_add_eq_mul, mul_smul,
      map_mul, Module.End.mul_apply, hfix, hde, map_mul, Module.End.mul_apply]
  have h2 : ∑ g : GL (ι₁ ⊕ ι₂) k,
      (if g.val.toBlocks₂₁ = 0 then N else 0) • ψ g.val.trace • ρ g v =
      N • N • gaussOp ψ (ρ.comp d) (gaussOp ψ (ρ.comp e) v) := by
    simp_rw [ite_smul, zero_smul]
    rw [← Finset.sum_filter, ← Finset.smul_sum, sum_lowerBlockZero]
    congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, hΦ]
    rw [gaussOp_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gaussOp_apply, map_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, map_smul]
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [smul_comm (ψ a.val.trace) (ψ D.val.trace)]
  have h3 : N • N • gaussOp ψ (ρ.comp d) (gaussOp ψ (ρ.comp e) v) = 0 := by
    rw [← h2, ← h1, hv, smul_zero]
  have h4 : gaussOp ψ (ρ.comp d) (gaussOp ψ (ρ.comp e) v) = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h hN
    rcases smul_eq_zero.mp h with h | h
    · exact absurd h hN
    exact h
  have h5 : gaussOp ψ (ρ.comp e) v = 0 := h₁ (ρ.comp d) (by rw [h4, map_zero])
  exact h₂ (ρ.comp e) (by rw [h5, map_zero])

end Block

/-! ### Small ranks -/

section SmallRank

variable [DecidableEq k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑_{a ∈ kˣ} ψ(a) = -1` for a nontrivial `ψ`. -/
theorem sum_units_addChar (hψ : ψ ≠ 1) : ∑ a : kˣ, ψ a = -1 := by
  have h0 := AddChar.sum_eq_zero_of_ne_one hψ
  rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, AddChar.map_zero_eq_one] at h0
  rw [Fintype.sum_equiv unitsEquivNeZero (fun a : kˣ => ψ a) (fun x => ψ x) (fun a => rfl)]
  linear_combination h0

/-- In rank one, `∑_g ψ(tr g) = ∑_{a ∈ kˣ} ψ(a) = -1`. -/
theorem sum_addChar_trace_of_card_eq_one (hψ : ψ ≠ 1) (hcard : Fintype.card ι = 1) :
    ∑ g : GL ι k, ψ g.val.trace = -1 := by
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hcard
  let : Unique ι := ⟨⟨i₀⟩, hi₀⟩
  have htr (M : Matrix ι ι k) : M.trace = M.det := by
    rw [Matrix.det_unique, Matrix.trace, Fintype.sum_unique]
    rfl
  have hbij : Function.Bijective (Matrix.GeneralLinearGroup.det : GL ι k →* kˣ) := by
    constructor
    · intro g g' h
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      obtain rfl : i = default := Subsingleton.elim _ _
      obtain rfl : j = default := Subsingleton.elim _ _
      have h' := congrArg Units.val h
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.det_unique, Matrix.det_unique] at h'
    · intro a
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => (a : k))
        (by rw [Matrix.det_unique]; exact a.ne_zero), Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      change (Matrix.of fun _ _ => (a : k)).det = a
      rw [Matrix.det_unique]
      rfl
  rw [← sum_units_addChar ψ hψ]
  refine Fintype.sum_bijective _ hbij _ _ fun g => ?_
  rw [htr, ← Matrix.GeneralLinearGroup.val_det_apply]

/-- Rank one: `S_0(v)` is fixed by the whole group, on which `T` acts by `-1`. -/
theorem gaussOp_injective_of_card_eq_one (hψ : ψ ≠ 1) (hcard : Fintype.card ι = 1)
    (ρ : Representation ℂ (GL ι k) V) : Function.Injective (gaussOp ψ ρ) := by
  apply gaussOp_injective_of_singular ψ hψ ρ
  intro v hv A hA
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hcard
  let : Unique ι := ⟨⟨i₀⟩, hi₀⟩
  have hA0 : A = 0 := by
    ext i j
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    rw [Matrix.det_unique] at hA
    exact hA
  subst hA0
  have hw (h : GL ι k) : ρ h (twistedGaussOp ψ 0 ρ v) = twistedGaussOp ψ 0 ρ v :=
    twistedGaussOp_fixed ψ 0 h (Matrix.zero_mul _) ρ v
  have hTw : gaussOp ψ ρ (twistedGaussOp ψ 0 ρ v) = 0 := by
    rw [gaussOp_twistedGaussOp, hv, map_zero]
  rw [gaussOp_apply] at hTw
  simp_rw [hw] at hTw
  rwa [← Finset.sum_smul, sum_addChar_trace_of_card_eq_one ψ hψ hcard, neg_one_smul,
    neg_eq_zero] at hTw

/-- Rank zero: every matrix is invertible. -/
theorem gaussOp_injective_of_isEmpty [IsEmpty ι] (hψ : ψ ≠ 1)
    (ρ : Representation ℂ (GL ι k) V) : Function.Injective (gaussOp ψ ρ) :=
  gaussOp_injective_of_singular ψ hψ ρ fun _ _ A hA =>
    absurd hA (by rw [Matrix.det_isEmpty]; exact one_ne_zero)

end SmallRank

/-! ### The induction on the rank -/

/-- The Gauss operator is injective for every representation of `GL_ι(k)`, by strong induction
on the cardinality `m` of `ι`. -/
theorem gaussOp_injective_of_card [DecidableEq k] (hψ : ψ ≠ 1) (m : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = m →
      ∀ ρ : Representation ℂ (GL ι k) V, Function.Injective (gaussOp ψ ρ) := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro ι _ _ hcard ρ
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
      exact gaussOp_injective_of_isEmpty ψ hψ ρ
    · exact gaussOp_injective_of_card_eq_one ψ hψ hcard ρ
  · apply gaussOp_injective_of_singular ψ hψ ρ
    intro v hv A hA
    obtain ⟨x, hx0, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
    have hdet : ((1 : Matrix ι ι k).updateCol j x).det ≠ 0 := by
      rw [← Matrix.cramer_apply, Matrix.cramer_one]
      exact hj
    let h := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
    have hcol (i : ι) : (A * h.val) i j = 0 := by
      have hi := congrFun hAx i
      change ∑ c, A i c * ((1 : Matrix ι ι k).updateCol j x) c j = 0
      simpa [Matrix.mulVec, dotProduct, Matrix.updateCol_self] using hi
    have hTw : gaussOp ψ ρ (twistedGaussOp ψ (A * h.val) ρ v) = 0 := by
      rw [gaussOp_twistedGaussOp, hv, map_zero]
    let e : ι ≃ {i // i = j} ⊕ {i // i ≠ j} := (Equiv.sumCompl (· = j)).symm
    have hc₁ : Fintype.card {i // i = j} < m := by
      rw [Fintype.card_subtype_eq]
      omega
    have hc₂ : Fintype.card {i // i ≠ j} < m := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    have hfixmat (X : Matrix {i // i = j} {i // i ≠ j} k) :
        A * h.val * (glReindex (k := k) e.symm (blockUnipotent X)).val = A * h.val := by
      ext a b
      rw [glReindex_val, blockUnipotent_val, Matrix.mul_apply]
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, e]
      rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)]
      · by_cases hb : b = j
        · rw [Equiv.sumCompl_symm_apply_of_pos (p := (· = j)) hb, fromBlocks_apply₁₁,
            Matrix.one_apply_eq, mul_one]
        · rw [Equiv.sumCompl_symm_apply_of_neg (p := (· = j)) hb, fromBlocks_apply₂₂,
            Matrix.one_apply_eq, mul_one]
      · intro c _ hcb
        by_cases hc : c = j
        · subst hc
          rw [hcol, zero_mul]
        · rw [Equiv.sumCompl_symm_apply_of_neg (p := (· = j)) hc]
          by_cases hb : b = j
          · rw [Equiv.sumCompl_symm_apply_of_pos (p := (· = j)) hb, fromBlocks_apply₂₁,
              Matrix.zero_apply, mul_zero]
          · rw [Equiv.sumCompl_symm_apply_of_neg (p := (· = j)) hb, fromBlocks_apply₂₂,
              Matrix.one_apply_ne (fun h => hcb (congrArg Subtype.val h)), mul_zero]
    have hw0 : twistedGaussOp ψ (A * h.val) ρ v = 0 := by
      refine eq_zero_of_blockUnipotent_fixed ψ hψ (IH _ hc₁ _ rfl) (IH _ hc₂ _ rfl)
        (ρ.comp (glReindex (k := k) e.symm).toMonoidHom) _ ?_ fun X => ?_
      · rw [gaussOp_comp_glReindex]
        exact hTw
      · exact twistedGaussOp_fixed ψ _ _ (hfixmat X) ρ v
    have h2 := twistedGaussOp_mul ψ A h ρ v
    rw [hw0] at h2
    have h3 := congrArg (ρ h) h2
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, eq_comm] at h3

end FiniteGauss

end Langlands.BushnellKutzko
