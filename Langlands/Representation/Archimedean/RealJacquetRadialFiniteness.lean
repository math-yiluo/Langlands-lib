import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof

/-!
# Radial finiteness with bounded coefficients

For a regular positive diagonal matrix `a`, put `r_{ab} = a_a / a_b` and, for `a < b`,
`L_{ab}(r) = E_{ab} - r_{ab}² E_{ba}`. Then `Ad(a) L_{ab}(r) = r_{ab} (E_{ab} - E_{ba})`, and
`𝔤 = span{L_{ab}(r)} ⊕ 𝔞 ⊕ 𝔨` as long as no `r_{ab}` equals `1`; for `r = 0` this is the
Iwasawa decomposition `𝔤 = 𝔫 ⊕ 𝔞 ⊕ 𝔨` behind the proof of `RealJacquetFiniteGenerationStatement`
in `RealJacquetFiniteGenerationProof`.

This file runs the word-reordering argument of that proof with the letters `L_{ab}(r)` in place
of the strictly upper triangular letters, uniformly in a parameter `q ∈ Q` on which `r` depends.
The coefficients that appear are products of the functions `r_{ab}²` and `(1 - r_{ab}²)⁻¹`; the
result is phrased for any subspace `S` of `Q → V` that is stable under multiplication by these
functions and under the letters `L_{ab}(r)` (`radial_finiteness`).

This is the radial-component step of Casselman's matrix-coefficient argument for
`V ≠ 𝔫V` (Wallach 1979, 4.13; Casselman–Miličić 1982), in an explicit form for `GL_n(ℝ)`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealJacquetRadial

open RealJacquetFiniteGeneration

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The pointwise action on `Q → V` -/

section Pointwise

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (Q : Type*)

/-- Endomorphisms of `V` act pointwise on `Q → V`. -/
def pointwise : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Q → V) where
  toFun A := LinearMap.pi fun q => A ∘ₗ LinearMap.proj q
  map_one' := LinearMap.ext fun _ => funext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  map_zero' := LinearMap.ext fun _ => funext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  commutes' _ := LinearMap.ext fun _ => funext fun _ => rfl

@[simp] theorem pointwise_apply (A : Module.End ℂ V) (f : Q → V) (q : Q) :
    pointwise Q A f q = A (f q) := rfl

variable {n : ℕ} (π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The pointwise action of `π` on `Q → V`. -/
def ptw : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ (Q → V) :=
  (pointwise Q).toLieHom.comp π

theorem op_ptw (X : Mat n) : op (ptw Q π) X = pointwise Q (op π X) := rfl

theorem wordOp_ptw (w : List (Mat n)) : wordOp (ptw Q π) w = pointwise Q (wordOp π w) := by
  induction w with
  | nil => simp
  | cons X w ih => rw [wordOp_cons, wordOp_cons, ih, op_ptw, map_mul]

theorem envelopingAction_ptw :
    envelopingAction (ptw Q π) = (pointwise Q).comp (envelopingAction π) := by
  symm
  refine (UniversalEnvelopingAlgebra.lift_unique ℂ (ptw Q π) _).1 ?_
  funext x
  simp [ptw]

theorem hasInfinitesimalCharacter_ptw (h : HasInfinitesimalCharacter π) :
    HasInfinitesimalCharacter (ptw Q π) := by
  intro z hz
  obtain ⟨c, hc⟩ := h z hz
  refine ⟨c, ?_⟩
  rw [envelopingAction_ptw, AlgHom.comp_apply, hc, AlgHom.commutes]

theorem diagEval_ptw : diagEval (ptw Q π) = (pointwise Q).comp (diagEval π) :=
  MvPolynomial.algHom_ext fun i => by simp [op_ptw]

end Pointwise

/-! ## Ring identities used in the reordering -/

section RingIdentities

variable {R : Type*} [Ring R]

theorem commutator_identity (X A B m : R) (h : X * m = m * X) :
    X * (A - m * B) = (A - m * B) * X + ((X * A - A * X) - m * (X * B - B * X)) := by
  calc X * (A - m * B) = X * A - (X * m) * B := by noncomm_ring
    _ = X * A - m * X * B := by rw [h]
    _ = _ := by noncomm_ring

theorem carry_identity (W X L Wv C₁ C₂ m : R) (hXL : X * L = L * X + (C₁ - m * C₂))
    (hW : W * m = m * W) :
    W * X * L * Wv = W * L * (X * Wv) + (W * (C₁ * Wv) - m * (W * (C₂ * Wv))) := by
  calc W * X * L * Wv = W * (X * L) * Wv := by noncomm_ring
    _ = W * L * (X * Wv) + (W * (C₁ * Wv) - (W * m) * (C₂ * Wv)) := by rw [hXL]; noncomm_ring
    _ = _ := by rw [hW]; noncomm_ring

theorem upper_identity (W L Wv mI mS K : R) (h₁ : W * mI = mI * W) (h₂ : W * mS = mS * W) :
    W * (mI * (L - mS * K) * Wv) = mI * (W * L * Wv - mS * (W * (K * Wv))) := by
  calc W * (mI * (L - mS * K) * Wv) = (W * mI) * (L * Wv) - (W * mI) * mS * (K * Wv) := by
        noncomm_ring
    _ = mI * W * (L * Wv) - mI * (W * mS) * (K * Wv) := by rw [h₁]; noncomm_ring
    _ = _ := by rw [h₂]; noncomm_ring

theorem lower_identity (W L Wv mI K : R) (h₁ : W * mI = mI * W) :
    W * (mI * (L - K) * Wv) = mI * (W * L * Wv - W * (K * Wv)) := by
  calc W * (mI * (L - K) * Wv) = (W * mI) * (L * Wv) - (W * mI) * (K * Wv) := by noncomm_ring
    _ = _ := by rw [h₁]; noncomm_ring

end RingIdentities

/-! ## Multiplication operators and the radial letters -/

section Letters

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V) {Q : Type*} (r : Q → Fin n → Fin n → ℝ)

/-- Multiplication by a function `c : Q → ℂ` on `Q → V`. -/
def mulOp (c : Q → ℂ) : Module.End ℂ (Q → V) := LinearMap.pi fun q => c q • LinearMap.proj q

@[simp] theorem mulOp_apply (c : Q → ℂ) (f : Q → V) (q : Q) : mulOp c f q = c q • f q := rfl

theorem mulOp_mul_pointwise (c : Q → ℂ) (A : Module.End ℂ V) :
    mulOp c * pointwise Q A = pointwise Q A * mulOp c :=
  LinearMap.ext fun f => funext fun q => by simp

theorem mulOp_mul_mulOp (c c' : Q → ℂ) : mulOp c * mulOp c' = (mulOp (c * c') : Module.End ℂ (Q → V)) :=
  LinearMap.ext fun f => funext fun q => by simp [mul_smul]

theorem mulOp_one : (mulOp (1 : Q → ℂ) : Module.End ℂ (Q → V)) = 1 :=
  LinearMap.ext fun f => funext fun q => by simp

theorem mulOp_sub (c c' : Q → ℂ) :
    (mulOp (c - c') : Module.End ℂ (Q → V)) = mulOp c - mulOp c' :=
  LinearMap.ext fun f => funext fun q => by simp [sub_smul]

/-- The function `q ↦ r_{ab}(q)²`. -/
def sq (a b : Fin n) : Q → ℂ := fun q => ((r q a b : ℂ)) ^ 2

/-- The radial letter `L_{ab}(r) = E_{ab} - r_{ab}² E_{ba}`, acting pointwise on `Q → V`. -/
def radLetter (a b : Fin n) : Module.End ℂ (Q → V) :=
  LinearMap.pi fun q => op π (E a b - (r q a b) ^ 2 • E b a) ∘ₗ LinearMap.proj q

@[simp] theorem radLetter_apply (a b : Fin n) (f : Q → V) (q : Q) :
    radLetter π r a b f q = op π (E a b - (r q a b) ^ 2 • E b a) (f q) := rfl

theorem radLetter_eq (a b : Fin n) :
    radLetter π r a b = op (ptw Q π) (E a b) - mulOp (sq r a b) * op (ptw Q π) (E b a) := by
  refine LinearMap.ext fun f => funext fun q => ?_
  simp only [radLetter_apply, op_sub, op_real_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, mulOp_apply, op_ptw, pointwise_apply, Pi.sub_apply, sq]
  push_cast
  rfl

variable {π}

theorem wordOp_ptw_mul_mulOp (w : List (Mat n)) (c : Q → ℂ) :
    wordOp (ptw Q π) w * mulOp c = mulOp c * wordOp (ptw Q π) w := by
  rw [wordOp_ptw, mulOp_mul_pointwise]

theorem op_ptw_mul_mulOp (X : Mat n) (c : Q → ℂ) :
    op (ptw Q π) X * mulOp c = mulOp c * op (ptw Q π) X := by
  rw [op_ptw, mulOp_mul_pointwise]

variable (π)

/-- The commutator of a constant letter with a radial letter. -/
theorem op_mul_radLetter (X : Mat n) (a b : Fin n) :
    op (ptw Q π) X * radLetter π r a b = radLetter π r a b * op (ptw Q π) X +
      (op (ptw Q π) (X * E a b - E a b * X) -
        mulOp (sq r a b) * op (ptw Q π) (X * E b a - E b a * X)) := by
  rw [radLetter_eq, op_commutator, op_commutator]
  exact commutator_identity _ _ _ _ (op_ptw_mul_mulOp (π := π) X (sq r a b))

end Letters

/-! ## The reordering argument -/

section Carry

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V} {Q : Type*} {r : Q → Fin n → Fin n → ℝ}
  {F S : Submodule ℂ (Q → V)} {d : ℕ}

theorem mulOp_mem_carry {c : Q → ℂ} (hc : ∀ s ∈ S, mulOp c s ∈ S) {A : Module.End ℂ (Q → V)}
    (hA : A ∈ carry F S) : mulOp c * A ∈ carry F S :=
  fun f hf => hc _ (hA f hf)

/-- A word with a radial letter `L_{ab}(r)` (`a < b`) carries `F` into `S`, if `S` is stable
under the radial letters and the multiplications by `r²`, and the words of smaller length
carry `F` into `S`: move the radial letter to the front. -/
theorem radial_upper {a b : Fin n}
    (hSL : ∀ s ∈ S, radLetter π r a b s ∈ S) (hS2 : ∀ s ∈ S, mulOp (sq r a b) s ∈ S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp (ptw Q π) w ∈ carry F S) :
    ∀ u v : List (Mat n), u.length + v.length < d →
      wordOp (ptw Q π) u * radLetter π r a b * wordOp (ptw Q π) v ∈ carry F S := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro v hv f hf
    simp only [wordOp_nil, one_mul, Module.End.mul_apply]
    exact hSL _ (hyp v (by simpa using hv) f hf)
  | append_singleton u X ih =>
    intro v hv
    have hsplit : wordOp (ptw Q π) (u ++ [X]) * radLetter π r a b * wordOp (ptw Q π) v =
        wordOp (ptw Q π) u * radLetter π r a b * wordOp (ptw Q π) (X :: v) +
          (wordOp (ptw Q π) (u ++ (X * E a b - E a b * X) :: v) -
            mulOp (sq r a b) * wordOp (ptw Q π) (u ++ (X * E b a - E b a * X) :: v)) := by
      simp only [wordOp_append, wordOp_cons, wordOp_nil, mul_one]
      exact carry_identity _ _ _ _ _ _ _ (op_mul_radLetter π r X a b)
        (wordOp_ptw_mul_mulOp u (sq r a b))
    rw [hsplit]
    simp only [List.length_append, List.length_singleton] at hv
    refine add_mem (ih (X :: v) (by simp; omega)) (sub_mem ?_ (mulOp_mem_carry hS2 ?_))
    · exact hyp _ (by simp; omega)
    · exact hyp _ (by simp; omega)

theorem one_sub_sq_ne_zero {a b : Fin n} {q : Q} (hr : r q a b ^ 2 ≠ 1) : 1 - sq r a b q ≠ 0 := by
  intro h
  apply hr
  have h' : ((r q a b : ℂ)) ^ 2 = 1 := by
    have := sub_eq_zero.1 h
    simpa [sq] using this.symm
  exact_mod_cast h'

theorem inv_mul_one_sub_sq {a b : Fin n} (hr : ∀ q, r q a b ^ 2 ≠ 1) :
    (fun q => (1 - sq r a b q)⁻¹) * (1 - sq r a b) = 1 :=
  funext fun q => by
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
    exact inv_mul_cancel₀ (one_sub_sq_ne_zero (hr q))

variable (π) in
/-- `E_{ab} = (1 - r_{ab}²)⁻¹ (L_{ab}(r) - r_{ab}² (E_{ab} - E_{ba}))`. -/
theorem op_E_eq_radLetter_upper (a b : Fin n) (hr : ∀ q, r q a b ^ 2 ≠ 1) :
    op (ptw Q π) (E a b) = mulOp (fun q => (1 - sq r a b q)⁻¹) *
      (radLetter π r a b - mulOp (sq r a b) * op (ptw Q π) (E a b - E b a)) := by
  have h1 : radLetter π r a b - mulOp (sq r a b) * op (ptw Q π) (E a b - E b a) =
      mulOp (1 - sq r a b) * op (ptw Q π) (E a b) := by
    rw [radLetter_eq, op_sub, mulOp_sub, mulOp_one, mul_sub, sub_mul, one_mul]
    abel
  rw [h1, ← mul_assoc, mulOp_mul_mulOp, inv_mul_one_sub_sq hr, mulOp_one, one_mul]

variable (π) in
/-- `E_{ab} = (1 - r_{ba}²)⁻¹ (L_{ba}(r) - (E_{ba} - E_{ab}))`. -/
theorem op_E_eq_radLetter_lower (a b : Fin n) (hr : ∀ q, r q b a ^ 2 ≠ 1) :
    op (ptw Q π) (E a b) = mulOp (fun q => (1 - sq r b a q)⁻¹) *
      (radLetter π r b a - op (ptw Q π) (E b a - E a b)) := by
  have h1 : radLetter π r b a - op (ptw Q π) (E b a - E a b) =
      mulOp (1 - sq r b a) * op (ptw Q π) (E a b) := by
    rw [radLetter_eq, op_sub, mulOp_sub, mulOp_one, sub_mul, one_mul]
    abel
  rw [h1, ← mul_assoc, mulOp_mul_mulOp, inv_mul_one_sub_sq hr, mulOp_one, one_mul]

theorem transpose_E_sub_E (a b : Fin n) : (E a b - E b a : Mat n)ᵀ = -(E a b - E b a) := by
  rw [Matrix.transpose_sub, Matrix.transpose_single, Matrix.transpose_single, neg_sub]

variable (π r) in
/-- `S` is stable under the radial letters `L_{ab}(r)` and the multiplications by `r_{ab}²` and
`(1 - r_{ab}²)⁻¹`, for `a < b`. -/
structure IsRadialStable (S : Submodule ℂ (Q → V)) : Prop where
  letter_mem : ∀ a b : Fin n, a < b → ∀ s ∈ S, radLetter π r a b s ∈ S
  sq_mem : ∀ a b : Fin n, a < b → ∀ s ∈ S, mulOp (sq r a b) s ∈ S
  inv_mem : ∀ a b : Fin n, a < b → ∀ s ∈ S, mulOp (fun q => (1 - sq r a b q)⁻¹) s ∈ S

/-- A word with an off-diagonal matrix unit carries `F` into `S`, under the induction
hypothesis: write the matrix unit through a radial letter and an antisymmetric letter. -/
theorem radial_offDiag (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op (ptw Q π) Y f ∈ F)
    (hS : IsRadialStable π r S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp (ptw Q π) w ∈ carry F S)
    {a b : Fin n} (hab : a ≠ b) (u v : List (Mat n)) (hw : u.length + v.length + 1 = d) :
    wordOp (ptw Q π) (u ++ E a b :: v) ∈ carry F S := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hsplit : wordOp (ptw Q π) (u ++ E a b :: v) =
        mulOp (fun q => (1 - sq r a b q)⁻¹) *
          (wordOp (ptw Q π) u * radLetter π r a b * wordOp (ptw Q π) v -
            mulOp (sq r a b) * wordOp (ptw Q π) (u ++ (E a b - E b a) :: v)) := by
      simp only [wordOp_append, wordOp_cons]
      rw [op_E_eq_radLetter_upper π a b (fun q => hr q a b h)]
      exact upper_identity _ _ _ _ _ _ (wordOp_ptw_mul_mulOp u _) (wordOp_ptw_mul_mulOp u _)
    rw [hsplit]
    refine mulOp_mem_carry (hS.inv_mem a b h) (sub_mem ?_ (mulOp_mem_carry (hS.sq_mem a b h) ?_))
    · exact radial_upper (hS.letter_mem a b h) (hS.sq_mem a b h) hyp u v (by omega)
    · exact wordOp_mem_carry_of_skew hF hyp (by simp; omega) (by simp) (transpose_E_sub_E a b)
  · have hsplit : wordOp (ptw Q π) (u ++ E a b :: v) =
        mulOp (fun q => (1 - sq r b a q)⁻¹) *
          (wordOp (ptw Q π) u * radLetter π r b a * wordOp (ptw Q π) v -
            wordOp (ptw Q π) (u ++ (E b a - E a b) :: v)) := by
      simp only [wordOp_append, wordOp_cons]
      rw [op_E_eq_radLetter_lower π a b (fun q => hr q b a h)]
      exact lower_identity _ _ _ _ _ (wordOp_ptw_mul_mulOp u _)
    rw [hsplit]
    refine mulOp_mem_carry (hS.inv_mem b a h) (sub_mem ?_ ?_)
    · exact radial_upper (hS.letter_mem b a h) (hS.sq_mem b a h) hyp u v (by omega)
    · exact wordOp_mem_carry_of_skew hF hyp (by simp; omega) (by simp) (transpose_E_sub_E b a)

/-- A word with a letter of zero diagonal carries `F` into `S`, under the induction hypothesis. -/
theorem radial_zeroDiag (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op (ptw Q π) Y f ∈ F)
    (hS : IsRadialStable π r S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp (ptw Q π) w ∈ carry F S)
    {w : List (Mat n)} (hw : w.length = d) {Z : Mat n} (hZ : Z ∈ w) (hZd : ∀ i, Z i i = 0) :
    wordOp (ptw Q π) w ∈ carry F S := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hZ
  rw [wordOp_eq_sum_E]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  rcases eq_or_ne a b with rfl | hab
  · rw [hZd, Complex.ofReal_zero, zero_smul]; exact zero_mem _
  · exact Submodule.smul_mem _ _
      (radial_offDiag hr hF hS hyp hab u v (by simp at hw; omega))

/-- Reduction to words in the diagonal matrix units (as `wordOp_mem_carry_of_diag_prefix`). -/
theorem radial_diag_prefix (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op (ptw Q π) Y f ∈ F)
    (hS : IsRadialStable π r S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp (ptw Q π) w ∈ carry F S)
    (hdiag : ∀ idx : List (Fin n), idx.length = d → wordOp (ptw Q π) (idx.map D) ∈ carry F S) :
    ∀ (u : List (Mat n)) (idx : List (Fin n)), idx.length + u.length = d →
      wordOp (ptw Q π) (idx.map D ++ u) ∈ carry F S := by
  intro u
  induction u with
  | nil => intro idx h; simpa using hdiag idx (by simpa using h)
  | cons X u ih =>
    intro idx h
    rw [wordOp_eq_sum_E]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ ?_
    rcases eq_or_ne a b with rfl | hab
    · have := ih (idx ++ [a]) (by simp at h ⊢; omega)
      simpa [List.map_append, List.append_assoc] using this
    · exact radial_offDiag hr hF hS hyp hab (idx.map D) u (by simp at h ⊢; omega)

theorem radial_zdSpan_le_carry (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op (ptw Q π) Y f ∈ F)
    (hS : IsRadialStable π r S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp (ptw Q π) w ∈ carry F S) :
    zdSpan (ptw Q π) d ≤ carry F S := by
  rw [zdSpan, Submodule.span_le]
  rintro _ ⟨w, hw, ⟨X, hX, hXd⟩, rfl⟩
  exact radial_zeroDiag hr hF hS hyp hw hX hXd

open MvPolynomial in
theorem radial_diagEval_mem_carry (hinf : HasInfinitesimalCharacter π)
    (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op (ptw Q π) Y f ∈ F)
    (hS : IsRadialStable π r S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp (ptw Q π) w ∈ carry F S)
    {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ powerSumSpan n d) :
    diagEval (ptw Q π) p ∈ carry F S := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, l, hl, hdeg, rfl⟩ := hx
    obtain ⟨idx, hlen, hprod⟩ := exists_list_of_monomial (n := n) γ
    obtain ⟨c, Z, hZ, hpsum⟩ := diagEval_psum (ptw Q π) (hasInfinitesimalCharacter_ptw Q π hinf) l
    have hγ : diagEval (ptw Q π) (monomial γ 1) = wordOp (ptw Q π) (idx.map D) := by
      rw [wordOp_map_D, hprod]
    rw [map_mul, hpsum, hγ, mul_sub, mul_smul_comm, mul_one]
    refine sub_mem (Submodule.smul_mem _ _ (hyp _ (by rw [List.length_map]; omega))) ?_
    have := wordOp_mul_mem_zdSpan (ptw Q π) (idx.map D) hZ
    rw [List.length_map, hlen, hdeg] at this
    exact radial_zdSpan_le_carry hr hF hS hyp this
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

open MvPolynomial in
theorem radial_diag_mem_carry (hinf : HasInfinitesimalCharacter π)
    (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op (ptw Q π) Y f ∈ F)
    (hS : IsRadialStable π r S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp (ptw Q π) w ∈ carry F S)
    (hbox : boxSpace (ptw Q π) F ≤ S) (idx : List (Fin n)) (hidx : idx.length = d) :
    wordOp (ptw Q π) (idx.map D) ∈ carry F S := by
  obtain ⟨γ, hγ, hprod⟩ := exists_monomial_of_list (n := n) idx
  rw [wordOp_map_D, hprod]
  by_cases hsmall : ∀ i, γ i < n
  · exact mem_carry.2 fun f hf => hbox (mem_boxSpace (ptw Q π) hsmall hf)
  · simp only [not_forall, not_lt] at hsmall
    obtain ⟨i, hi⟩ := hsmall
    have := monomial_mem_powerSumSpan (n := n) hi
    rw [hγ, hidx] at this
    exact radial_diagEval_mem_carry hinf hr hF hS hyp this

/-- Every word carries `F` into `S`. -/
theorem radial_wordOp_mem_carry (hinf : HasInfinitesimalCharacter π)
    (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op (ptw Q π) Y f ∈ F)
    (hS : IsRadialStable π r S) (hbox : boxSpace (ptw Q π) F ≤ S) (w : List (Mat n)) :
    wordOp (ptw Q π) w ∈ carry F S := by
  suffices h : ∀ m, ∀ w : List (Mat n), w.length = m → wordOp (ptw Q π) w ∈ carry F S from
    h _ w rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hyp : ∀ w : List (Mat n), w.length < m → wordOp (ptw Q π) w ∈ carry F S :=
      fun w hw => ih _ hw w rfl
    intro w hw
    have := radial_diag_prefix hr hF hS hyp
      (fun idx hidx => radial_diag_mem_carry hinf hr hF hS hyp hbox idx hidx) w []
      (by simpa using hw)
    simpa using this

end Carry

/-! ## Radial finiteness for constant functions -/

section Finiteness

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V} {Q : Type*} {r : Q → Fin n → Fin n → ℝ}

/-- Constant functions `Q → V`. -/
def constMap (Q V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℂ] (Q → V) :=
  LinearMap.pi fun _ => LinearMap.id

@[simp] theorem constMap_apply (v : V) (q : Q) : constMap Q V v q = v := rfl

theorem pointwise_constMap (A : Module.End ℂ V) (v : V) :
    pointwise Q A (constMap Q V v) = constMap Q V (A v) := rfl

/-- **Radial finiteness.** Let `F ⊆ V` be stable under the antisymmetric matrices and let `S` be
a subspace of `Q → V` that is stable under the radial letters `L_{ab}(r)` and the
multiplications by `r_{ab}²` and `(1 - r_{ab}²)⁻¹` (`a < b`), and contains the constant functions
with values in the box space of `F`. If `π` has an infinitesimal character and no `r_{ab}(q)²`
equals `1`, then for every word `w` and `f ∈ F` the constant function `w · f` lies in `S`. -/
theorem radial_finiteness (hinf : HasInfinitesimalCharacter π)
    (hr : ∀ q a b, a < b → r q a b ^ 2 ≠ 1) {F : Submodule ℂ V}
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F) {S : Submodule ℂ (Q → V)}
    (hS : IsRadialStable π r S) (hbox : ∀ u ∈ boxSpace π F, constMap Q V u ∈ S)
    (w : List (Mat n)) {f : V} (hf : f ∈ F) : constMap Q V (wordOp π w f) ∈ S := by
  have hF' : ∀ Y : Mat n, Yᵀ = -Y → ∀ g ∈ F.map (constMap Q V),
      op (ptw Q π) Y g ∈ F.map (constMap Q V) := by
    rintro Y hY _ ⟨g, hg, rfl⟩
    exact ⟨op π Y g, hF Y hY g hg, rfl⟩
  have hbox' : boxSpace (ptw Q π) (F.map (constMap Q V)) ≤ S := by
    refine iSup_le fun β => ?_
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    rw [diagEval_ptw, AlgHom.comp_apply]
    exact hbox _ (Submodule.mem_iSup_of_mem β ⟨g, hg, rfl⟩)
  have := radial_wordOp_mem_carry hinf hr hF' hS hbox' w _ ⟨f, hf, rfl⟩
  rwa [wordOp_ptw] at this

end Finiteness

end RealJacquetRadial

end Langlands.Archimedean
