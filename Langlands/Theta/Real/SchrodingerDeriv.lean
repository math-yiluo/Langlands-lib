import Langlands.Theta.Real.Schrodinger

/-!
# The derived Schrödinger representation and the oscillator representation of `sp`

On Schwartz space, `schrodingerDeriv w` is the derivative at `t = 0` of the Schrödinger operators
of `t • w`: for `w = (p, q)`, `schrodingerDeriv w f = ∂_p f + 2πi⟨q, x⟩ f`. These operators span
a representation of the Heisenberg Lie algebra:

`[schrodingerDeriv w, schrodingerDeriv w'] = 2πi ω(w, w')`

for the standard symplectic form `ω` (`schrodingerDeriv_commutator`).

For a matrix `X`, `oscillatorDeriv X` is the quadratic expression
`(4πi)⁻¹ ∑ₐ,ᵦ (XJ)ₐᵦ / 2 · (Dₐ Dᵦ + Dᵦ Dₐ)` in the operators `Dₐ = schrodingerDeriv eₐ` of the
standard basis. For `X` in the symplectic Lie algebra `sp`, it satisfies
`[oscillatorDeriv X, schrodingerDeriv w] = schrodingerDeriv (X w)`
(`oscillatorDeriv_commutator`): it is the infinitesimal oscillator (metaplectic) representation of
`X`. For `X = [[A, B], [C, D]]` it is the second-order operator
`(4πi)⁻¹ ∑ B_{jk} ∂_j ∂_k - ∑ A_{jk} x_k ∂_j - tr A / 2 - πi ∑ C_{jk} x_j x_k`
(`oscillatorDeriv_fromBlocks_apply`). G. B. Folland, *Harmonic analysis in phase space* (1989),
chapter 1, §3, p. 21 (`dρ(p, q, t) = 2πi(pD + qX + tI)` with `D = (2πi)⁻¹ ∂` (Prologue, p. 3), a
Lie algebra homomorphism for the bracket (1.15) of the Heisenberg Lie algebra, p. 18), and
chapter 4, §3, Proposition (4.43), formula (4.44) and Theorem (4.45), p. 186 (`2πi P_A(D, X)`, the
explicit operator above, is the infinitesimal metaplectic representation).
-/

noncomputable section

open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff InnerProductSpace

namespace Langlands.Theta

variable {l : Type} [Fintype l]

open Langlands.Theta.Real.Internal

namespace Real

/-- The derived Schrödinger operator of `w = (p, q)` on Schwartz space:
`f ↦ ∂_p f + 2πi⟨q, ·⟩ f`. -/
def schrodingerDeriv (w : l ⊕ l → ℝ) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  lineDerivOpCLM ℂ (RealSchwartz l) (translationPart w) +
    (2 * π * I : ℂ) • smulLeftCLM ℂ fun x : EuclideanSpace ℝ l => ((⟪modulationPart w, x⟫ : ℝ) : ℂ)

/-- `schrodingerDeriv w f x = ∂_p f(x) + 2πi⟨q, x⟩ f(x)` for `w = (p, q)`. -/
theorem schrodingerDeriv_apply (w : l ⊕ l → ℝ) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) :
    schrodingerDeriv w f x = fderiv ℝ f x (translationPart w) + 2 * π * I * (⟪modulationPart w, x⟫ : ℝ) * f x := by
  have h : (fun x : EuclideanSpace ℝ l => ((⟪modulationPart w, x⟫ : ℝ) : ℂ)).HasTemperateGrowth :=
    (ofRealCLM.comp (innerSL ℝ (modulationPart w))).hasTemperateGrowth
  simp [schrodingerDeriv, h, lineDerivOp_apply_eq_fderiv, mul_assoc]

namespace Internal

theorem hasDerivAt_rhoFun (w : l ⊕ l → ℝ) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (schrodingerDeriv w f x) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * π * (t * ⟪modulationPart w, x⟫) + π * (t * (t * ⟪translationPart w, modulationPart w⟫)))
      (2 * π * ⟪modulationPart w, x⟫) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const ⟪modulationPart w, x⟫).const_mul (2 * π)).add
      (((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const ⟪translationPart w, modulationPart w⟫)).const_mul π)
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  have h3 : HasDerivAt (fun t : ℝ => x + t • translationPart w) (translationPart w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (translationPart w)).const_add x
  have h4 : HasDerivAt (fun t : ℝ => f (x + t • translationPart w)) (fderiv ℝ f x (translationPart w)) 0 := by
    have := (f.hasFDerivAt (x + (0 : ℝ) • translationPart w)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul h4
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => ?_)
  · rw [schrodingerDeriv_apply]
    simp
    ring
  · simp only [rhoFun, schrodingerPhase, translationPart_smul, modulationPart_smul, real_inner_smul_left, real_inner_smul_right, Pi.mul_apply]

end Internal

/-- `schrodingerDeriv` is additive in `w`. -/
theorem schrodingerDeriv_add (w w' : l ⊕ l → ℝ) : schrodingerDeriv (w + w') = schrodingerDeriv w + schrodingerDeriv w' := by
  ext f x
  simp only [_root_.add_apply, _root_.add_apply, schrodingerDeriv_apply, translationPart_add, modulationPart_add, inner_add_left,
    map_add, ofReal_add]
  ring

/-- `schrodingerDeriv` is real-linear in `w`. -/
theorem schrodingerDeriv_smul (t : ℝ) (w : l ⊕ l → ℝ) : schrodingerDeriv (t • w) = (t : ℂ) • schrodingerDeriv w := by
  ext f x
  simp only [_root_.smul_apply, _root_.smul_apply, schrodingerDeriv_apply, translationPart_smul, modulationPart_smul,
    real_inner_smul_left, map_smul, ofReal_mul, smul_eq_mul, real_smul]
  ring

namespace Internal

theorem schrodingerDeriv_comm_sympl (w w' : l ⊕ l → ℝ) :
    schrodingerDeriv w * schrodingerDeriv w' - schrodingerDeriv w' * schrodingerDeriv w = (2 * π * I * sympl w w' : ℂ) • (1 : RealSchwartz l →L[ℂ] RealSchwartz l) := by
  have key : ∀ (u v : l ⊕ l → ℝ) (f : RealSchwartz l) (x : EuclideanSpace ℝ l), fderiv ℝ (schrodingerDeriv v f) x (translationPart u) =
      fderiv ℝ (fderiv ℝ f) x (translationPart u) (translationPart v) + (2 * π * I * (⟪modulationPart v, translationPart u⟫ : ℝ) * f x +
        2 * π * I * (⟪modulationPart v, x⟫ : ℝ) * fderiv ℝ f x (translationPart u)) := by
    intro u v f x
    have e : ⇑(schrodingerDeriv v f) = fun y => fderiv ℝ f y (translationPart v) + 2 * π * I * (⟪modulationPart v, y⟫ : ℝ) * f y :=
      funext (schrodingerDeriv_apply v f)
    have d1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      (fderivCLM ℂ _ _ f).differentiableAt.hasFDerivAt
    have d2 := d1.clm_apply (hasFDerivAt_const (translationPart v) x)
    have d3 := ((ofRealCLM.comp (innerSL ℝ (modulationPart v))).hasFDerivAt (x := x)).const_mul (2 * π * I : ℂ)
    have d4 := d2.add (d3.mul (f.hasFDerivAt x))
    rw [e]
    refine (congrArg (fun L : EuclideanSpace ℝ l →L[ℝ] ℂ => L (translationPart u)) d4.fderiv).trans ?_
    simp
    ring
  ext f x
  have hs : fderiv ℝ (fderiv ℝ f) x (translationPart w) (translationPart w') = fderiv ℝ (fderiv ℝ f) x (translationPart w') (translationPart w) :=
    ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _
  simp only [_root_.sub_apply, mul_apply_eq_comp, _root_.sub_apply,
    _root_.smul_apply, one_apply_eq_self, _root_.smul_apply, smul_eq_mul]
  rw [schrodingerDeriv_apply w (schrodingerDeriv w' f), schrodingerDeriv_apply w' (schrodingerDeriv w f), key, key, schrodingerDeriv_apply, schrodingerDeriv_apply, hs]
  simp only [sympl, real_inner_comm (translationPart w) (modulationPart w'), ofReal_sub]
  ring

end Internal

/-- The canonical commutation relations: `[D(w), D(w')] = 2πi ω(w, w')` for the standard
symplectic form `ω`. -/
theorem schrodingerDeriv_commutator (w w' : l ⊕ l → ℝ) :
    schrodingerDeriv w * schrodingerDeriv w' - schrodingerDeriv w' * schrodingerDeriv w =
      (2 * π * I * stdSymplecticForm l ℝ w w' : ℂ) • (1 : RealSchwartz l →L[ℂ] RealSchwartz l) := by
  rw [schrodingerDeriv_comm_sympl, sympl_eq_stdSymplecticForm]

variable [DecidableEq l]

/-- The infinitesimal oscillator representation of a matrix `X`:
`(4πi)⁻¹ ∑ₐ,ᵦ (XJ)ₐᵦ / 2 · (Dₐ Dᵦ + Dᵦ Dₐ)` with `Dₐ = schrodingerDeriv (Pi.single a 1)`. -/
def oscillatorDeriv (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  (4 * π * I : ℂ)⁻¹ • ∑ a, ∑ b, (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (schrodingerDeriv (Pi.single a 1) * schrodingerDeriv (Pi.single b 1) + schrodingerDeriv (Pi.single b 1) * schrodingerDeriv (Pi.single a 1))

namespace Internal

theorem mul_J_symm {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    (X * Matrix.J l ℝ)ᵀ = X * Matrix.J l ℝ := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have h2 := congrArg (fun Y => Matrix.J l ℝ * Y * Matrix.J l ℝ) h
  simp only [Matrix.mul_assoc, J_squared] at h2
  simp only [← Matrix.mul_assoc, J_squared] at h2
  rw [transpose_mul, J_transpose]
  simpa using h2

end Internal

/-- `schrodingerDeriv w` in the standard basis. -/
theorem schrodingerDeriv_eq_sum (w : l ⊕ l → ℝ) : schrodingerDeriv w = ∑ a, (w a : ℂ) • schrodingerDeriv (Pi.single a 1) := by
  let L : (l ⊕ l → ℝ) →+ (RealSchwartz l →L[ℂ] RealSchwartz l) := AddMonoidHom.mk' schrodingerDeriv schrodingerDeriv_add
  have : w = ∑ a, w a • (Pi.single a 1 : l ⊕ l → ℝ) := by
    ext b
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  exact (map_sum L _ _).trans (Finset.sum_congr rfl fun a _ => schrodingerDeriv_smul _ _)

namespace Internal

theorem sympl_eq (w u : l ⊕ l → ℝ) : sympl w u = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ u) := by
  rw [sympl_eq_stdSymplecticForm, stdSymplecticForm_apply]

theorem sympl_single (b : l ⊕ l) (u : l ⊕ l → ℝ) : sympl (Pi.single b 1) u = -(Matrix.J l ℝ *ᵥ u) b := by
  rcases b with b | b <;>
    simp [sympl, translationPart, modulationPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]

end Internal

/-- For `X ∈ sp`: `[oscillatorDeriv X, schrodingerDeriv w] = schrodingerDeriv (X w)`. -/
theorem oscillatorDeriv_commutator {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (u : l ⊕ l → ℝ) :
    oscillatorDeriv X * schrodingerDeriv u - schrodingerDeriv u * oscillatorDeriv X = schrodingerDeriv (X *ᵥ u) := by
  set S := X * Matrix.J l ℝ with hS
  have hsym : ∀ a b, S a b = S b a := fun a b => (congrFun (congrFun (mul_J_symm hX) b) a)
  set s : l ⊕ l → ℝ := fun b => sympl (Pi.single b 1) u with hs
  have hXu : ∀ a, (X *ᵥ u) a = ∑ b, S a b * s b := by
    intro a
    have : X *ᵥ u = S *ᵥ (-(Matrix.J l ℝ *ᵥ u)) := by
      rw [mulVec_neg, mulVec_mulVec, hS, Matrix.mul_assoc, J_squared]
      simp [neg_mulVec]
    rw [this]
    simp only [hs, sympl_single]
    rfl
  set D : l ⊕ l → (RealSchwartz l →L[ℂ] RealSchwartz l) := fun a => schrodingerDeriv (Pi.single a 1) with hD
  have hc : ∀ a, D a * schrodingerDeriv u = schrodingerDeriv u * D a + (2 * π * I * s a : ℂ) • 1 := fun a => by
    rw [← schrodingerDeriv_comm_sympl]
    simp [hD]
  have h2 : ∀ a b, (D a * D b + D b * D a) * schrodingerDeriv u - schrodingerDeriv u * (D a * D b + D b * D a) =
      (4 * π * I : ℂ) • ((s b : ℂ) • D a + (s a : ℂ) • D b) := fun a b => by
    have e : ∀ a b, D a * D b * schrodingerDeriv u = schrodingerDeriv u * (D a * D b) +
        ((2 * π * I * s a : ℂ) • D b + (2 * π * I * s b : ℂ) • D a) := fun a b => by
      rw [mul_assoc, hc b, mul_add, ← mul_assoc, hc a, add_mul, mul_assoc, add_assoc]
      simp
    rw [add_mul, e, e, mul_add]
    module
  have hne : (4 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : oscillatorDeriv X * schrodingerDeriv u - schrodingerDeriv u * oscillatorDeriv X =
      ∑ a, ∑ b, ((S a b / 2 : ℝ) : ℂ) • ((s b : ℂ) • D a + (s a : ℂ) • D b) := by
    simp only [oscillatorDeriv, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      ← Finset.sum_sub_distrib]
    rw [inv_smul_eq_iff₀ hne]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm (4 * π * I : ℂ), ← h2]
  rw [h3, schrodingerDeriv_eq_sum (X *ᵥ u)]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => ((S a b / 2 : ℝ) : ℂ) • (s a : ℂ) • D b), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hXu, ← Finset.sum_add_distrib, ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hsym b a]
  push_cast
  module

/-- The derived operator of the `j`-th translation coordinate is the partial derivative `∂ⱼ`. -/
theorem schrodingerDeriv_single_inl (j : l) (f : RealSchwartz l) :
    schrodingerDeriv (Pi.single (Sum.inl j) 1) f = ∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)} f := by
  have h1 : translationPart (Pi.single (Sum.inl j) 1 : l ⊕ l → ℝ) = EuclideanSpace.single j 1 := by
    ext i
    simp [translationPart, Pi.single_apply]
  have h2 : modulationPart (Pi.single (Sum.inl j) 1 : l ⊕ l → ℝ) = 0 := by
    ext i
    simp [modulationPart]
  ext x
  simp [schrodingerDeriv_apply, h1, h2, lineDerivOp_apply_eq_fderiv]

/-- The derived operator of the `k`-th modulation coordinate is multiplication by `2πi xₖ`. -/
theorem schrodingerDeriv_single_inr (k : l) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) :
    schrodingerDeriv (Pi.single (Sum.inr k) 1) f x = 2 * π * I * x k * f x := by
  have h1 : translationPart (Pi.single (Sum.inr k) 1 : l ⊕ l → ℝ) = 0 := by
    ext i
    simp [translationPart]
  have h2 : modulationPart (Pi.single (Sum.inr k) 1 : l ⊕ l → ℝ) = EuclideanSpace.single k 1 := by
    ext i
    simp [modulationPart, Pi.single_apply]
  simp [schrodingerDeriv_apply, h1, h2, EuclideanSpace.inner_single_left]

/-- The oscillator operator of `[[A, B], [C, D]] ∈ sp` as a differential operator: `(4πi)⁻¹ ∑ B_{jk}
∂ⱼ∂ₖ f - ∑ A_{jk} xₖ ∂ⱼ f - tr A / 2 · f - πi ∑ C_{jk} xⱼ xₖ f`. -/
theorem oscillatorDeriv_fromBlocks_apply {A B C D : Matrix l l ℝ} (hX : fromBlocks A B C D ∈ LieAlgebra.Symplectic.sp l ℝ)
    (f : RealSchwartz l) (x : EuclideanSpace ℝ l) :
    oscillatorDeriv (fromBlocks A B C D) f x =
      (4 * π * I : ℂ)⁻¹ * ∑ j, ∑ k, (B j k : ℂ) * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)}
          (∂_{(EuclideanSpace.single k 1 : EuclideanSpace ℝ l)} f)) x
        - ∑ j, ∑ k, (A j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)} f) x
        - (A.trace : ℝ) / 2 * f x - π * I * ∑ j, ∑ k, (C j k : ℂ) * x j * x k * f x := by
  have hS : fromBlocks A B C D * Matrix.J l ℝ = fromBlocks B (-A) D (-C) := by
    simp [Matrix.J, fromBlocks_multiply]
  have hsym := mul_J_symm hX
  rw [hS] at hsym
  have hD : ∀ j k, D j k = -A k j := fun j k => congrFun (congrFun hsym (Sum.inl k)) (Sum.inr j)
  have hne : (4 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  set P : l → (RealSchwartz l →L[ℂ] RealSchwartz l) := fun j => schrodingerDeriv (Pi.single (Sum.inl j) 1) with hP
  set Q : l → (RealSchwartz l →L[ℂ] RealSchwartz l) := fun j => schrodingerDeriv (Pi.single (Sum.inr j) 1) with hQ
  have hPP : ∀ j k, P k * P j = P j * P k := fun j k => by
    have := schrodingerDeriv_comm_sympl (l := l) (Pi.single (Sum.inl k) 1) (Pi.single (Sum.inl j) 1)
    rw [sympl_single] at this
    rw [← sub_eq_zero, this]
    simp [Matrix.J]
  have hPQ : ∀ j k, P j * Q k = Q k * P j + (2 * π * I * (if j = k then 1 else 0) : ℂ) • 1 := fun j k => by
    have := schrodingerDeriv_comm_sympl (l := l) (Pi.single (Sum.inl j) 1) (Pi.single (Sum.inr k) 1)
    rw [sympl_single] at this
    rw [← sub_eq_iff_eq_add', this]
    by_cases h : j = k <;> simp [Matrix.J, h]
  have hQa : ∀ k (g : RealSchwartz l), Q k g x = 2 * π * I * x k * g x := fun k g => schrodingerDeriv_single_inr k g x
  have hq : oscillatorDeriv (fromBlocks A B C D) = (4 * π * I : ℂ)⁻¹ • ((∑ j, ∑ k, (B j k : ℂ) • (P j * P k)) -
      (∑ j, ∑ k, (2 * A j k : ℂ) • (Q k * P j)) - (2 * π * I * (A.trace : ℝ) : ℂ) • 1 -
      ∑ j, ∑ k, (C j k / 2 : ℂ) • (Q j * Q k + Q k * Q j)) := by
    rw [oscillatorDeriv, hS]
    congr 1
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply, hD]
    have t : (2 * π * I * (A.trace : ℝ) : ℂ) • (1 : RealSchwartz l →L[ℂ] RealSchwartz l) =
        ∑ j, ∑ k, (A j k : ℂ) • (2 * π * I * (if j = k then 1 else 0) : ℂ) • (1 : RealSchwartz l →L[ℂ] RealSchwartz l) := by
      simp only [Matrix.trace, diag_apply, ofReal_sum, Finset.mul_sum, Finset.sum_smul, smul_smul, mul_ite, mul_one,
        mul_zero, ite_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    rw [t, Finset.sum_comm (f := fun j k => ((-A k j / 2 : ℝ) : ℂ) • _)]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    change ((B j k / 2 : ℝ) : ℂ) • (P j * P k + P k * P j) + ((-A j k / 2 : ℝ) : ℂ) • (Q k * P j + P j * Q k) +
      (((-A j k / 2 : ℝ) : ℂ) • (P j * Q k + Q k * P j) + ((-C j k / 2 : ℝ) : ℂ) • (Q j * Q k + Q k * Q j)) = _
    rw [hPP j k, hPQ j k]
    push_cast
    module
  rw [hq]
  simp only [_root_.smul_apply, _root_.sub_apply, _root_.sum_apply,
    _root_.add_apply, mul_apply_eq_comp, one_apply_eq_self,
    _root_.smul_apply, _root_.sub_apply, _root_.add_apply, _root_.sum_apply, smul_eq_mul, hQa]
  simp only [hP, schrodingerDeriv_single_inl, mul_sub, Finset.mul_sum]
  congr 1
  · congr 1
    · congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
      ring
    · field_simp
      ring
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    field_simp
    ring

end Real

end Langlands.Theta
