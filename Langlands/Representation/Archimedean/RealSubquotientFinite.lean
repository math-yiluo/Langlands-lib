import Langlands.Representation.Archimedean.RealSubquotientSymbol
import Mathlib.RingTheory.Nullstellensatz

/-!
# Gelfand elements, finiteness and nilpotency

Helper results for Harish-Chandra's subquotient theorem (`RealPrincipalSeriesSubquotientStatement`).

* `Cgel l = tr(E^l)`: Gelfand's central elements; `xiPoly τ z` the polynomial by which a central
  `z` acts on the principal series (`Q_central`); the degree-`l` part of `xiPoly τ (Cgel l)` is the
  power sum `p_l` (`xiPoly_Cgel_top`).
* `Bsub τ`: the `K`-invariant matrices over `U(𝔤)`, a subalgebra; `chat_diagonal_zeta`: the
  matrix `ĉ` of a polynomial in the Gelfand elements.
* `mem_spanBox`: `ℂ[a]` is spanned by the box monomials `a^β`, `β < n`, over the polynomials in
  the `ξ_l`; `finite_fibre`: the fibre `{a : ξ_l(a) = λ_l for all l}` is finite.
* `exists_monic_matrix_poly`: the determinant trick for a matrix over a finite algebra.
* `exists_pow_act_eq_zero` (**nilpotency**): a `K`-invariant `x` whose `ĉ(x)` vanishes on the
  fibre `{a : ξ_l(a) = λ_l}` acts nilpotently on every `K`-intertwiner into a module on which the
  Gelfand elements act by the scalars `λ_l`.
-/

noncomputable section

open scoped Matrix TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealSubquotient

open Kostant MvPolynomial Langlands.Algebra.UniversalEnveloping InfinitesimalCharacter

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ## Gelfand's central elements -/

/-- Gelfand's central element `tr(E^l)`, `E` the matrix of generators. -/
def Cgel (n l : ℕ) : UU n := Matrix.trace (RealJacquetFiniteGeneration.gen n ^ l)

theorem Cgel_mem_center (l : ℕ) : Cgel n l ∈ Subalgebra.center ℂ (UU n) :=
  RealJacquetFiniteGeneration.trace_gen_pow_mem_center n l

/-- The generic matrix `(X_pq)` of `𝔤𝔩_n`. -/
def genericMat (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Coord (fun _ : Unit => n)) ℂ) :=
  Matrix.of fun p q => X ⟨(), p, q⟩

theorem gen_apply (p q : Fin n) :
    RealJacquetFiniteGeneration.gen n p q =
      UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ Matrix.single p q (1 : ℝ)) := rfl

theorem gen_pow_mem_and_symbol : ∀ (l : ℕ) (p q : Fin n),
    (RealJacquetFiniteGeneration.gen n ^ l) p q ∈ degreeFiltration ℂ (LL n) l ∧
      (realSymbol n).symbol l ((RealJacquetFiniteGeneration.gen n ^ l) p q) = (genericMat n ^ l) p q := by
  intro l
  induction l with
  | zero =>
    intro p q
    simp only [pow_zero, Matrix.one_apply]
    split_ifs
    · refine ⟨algebraMap_mem_degreeFiltration ℂ (LL n) 1 0 |> fun h => by simpa using h, ?_⟩
      simpa using (realSymbol n).symbol_zero_algebraMap 1
    · exact ⟨Submodule.zero_mem _, map_zero _⟩
  | succ l ih =>
    intro p q
    have hg : ∀ r, RealJacquetFiniteGeneration.gen n r q ∈ degreeFiltration ℂ (LL n) 1 := by
      intro r
      rw [gen_apply, degreeFiltration_one]
      exact generator_mem_degreeOne ℂ (LL n) _
    rw [pow_succ, Matrix.mul_apply, pow_succ, Matrix.mul_apply]
    refine ⟨Submodule.sum_mem _ fun r _ => mul_mem_degreeFiltration ℂ (LL n) (ih p r).1 (hg r),
      ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [(realSymbol n).symbol_mul (ih p r).1 (hg r), (ih p r).2, gen_apply,
      SymbolData.symbol_one_ι, realSymbol_ξ_single]
    rfl

theorem Cgel_mem_degreeFiltration (l : ℕ) : Cgel n l ∈ degreeFiltration ℂ (LL n) l := by
  rw [Cgel, Matrix.trace]
  exact Submodule.sum_mem _ fun p _ => (gen_pow_mem_and_symbol l p p).1

theorem symbol_Cgel (l : ℕ) :
    (realSymbol n).symbol l (Cgel n l) = Matrix.trace (genericMat n ^ l) := by
  rw [Cgel, Matrix.trace, map_sum, Matrix.trace]
  exact Finset.sum_congr rfl fun p _ => (gen_pow_mem_and_symbol l p p).2

theorem diagRes_symbol_Cgel (l : ℕ) :
    diagRes n ((realSymbol n).symbol l (Cgel n l)) = psum (Fin n) ℂ l := by
  have hmap : (diagRes n).mapMatrix (genericMat n) =
      Matrix.diagonal fun p => (X p : MvPolynomial (Fin n) ℂ) := by
    ext p q
    by_cases h : p = q
    · subst h; simp [genericMat, diagRes]
    · simp [genericMat, diagRes, h]
  have hpow : ∀ p, diagRes n ((genericMat n ^ l) p p) =
      ((diagRes n).mapMatrix (genericMat n ^ l)) p p := fun p => rfl
  rw [symbol_Cgel, Matrix.trace, map_sum, psum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, hpow, map_pow, hmap, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
    Pi.pow_apply]

/-! ## The polynomial of a central element -/

variable {d : ℕ}

/-- The polynomial by which a central element acts on the principal series: `Q(z, e₀)₀`. -/
def xiPoly (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) (z : UU n) :
    MvPolynomial (Fin n) ℂ :=
  if h : 0 < d then Q τ z (Pi.single (⟨0, h⟩ : Fin d) 1) ⟨0, h⟩ else 0

/-- The `K`-invariant matrices over `U(𝔤)`, as a subalgebra. -/
def Bsub (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) :
    Subalgebra ℂ (Matrix (Fin d) (Fin d) (UU n)) where
  carrier := {b | InB τ b}
  mul_mem' {a b} ha hb k := by
    have hmap : (a * b).map (envMap (conjLie (orthUnit k))) =
        a.map (envMap (conjLie (orthUnit k))) * b.map (envMap (conjLie (orthUnit k))) :=
      Matrix.map_mul (f := (envMap (conjLie (orthUnit k))).toRingHom)
    rw [← Matrix.mul_assoc, ha k, Matrix.mul_assoc, hb k, ← Matrix.mul_assoc, hmap]
  add_mem' {a b} ha hb k := by
    have hmap : (a + b).map (envMap (conjLie (orthUnit k))) =
        a.map (envMap (conjLie (orthUnit k))) + b.map (envMap (conjLie (orthUnit k))) :=
      Matrix.map_add _ (map_add _) a b
    rw [Matrix.mul_add, ha k, hb k, hmap, Matrix.add_mul]
  algebraMap_mem' c k := by
    have hmap : (algebraMap ℂ (Matrix (Fin d) (Fin d) (UU n)) c).map
        (envMap (conjLie (orthUnit k))) = algebraMap ℂ _ c :=
      ((envMap (conjLie (orthUnit k))).mapMatrix (m := Fin d)).commutes c
    change _ * algebraMap ℂ _ c = (algebraMap ℂ (Matrix (Fin d) (Fin d) (UU n)) c).map _ * _
    rw [hmap, Algebra.commutes]

theorem mem_Bsub {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
    {b : Matrix (Fin d) (Fin d) (UU n)} : b ∈ Bsub τ ↔ InB τ b := Iff.rfl

/-- A diagonal matrix with a central entry is `K`-invariant. -/
theorem diagonal_mem_Bsub {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
    {z : UU n} (hz : z ∈ Subalgebra.center ℂ (UU n)) :
    Matrix.diagonal (fun _ : Fin d => z) ∈ Bsub τ := by
  intro k
  have hAd : envMap (conjLie (orthUnit k)) z = z :=
    fixesCenter_of_det_ne_zero _ (det_ne_zero_of_orth k) (orthUnit k) (orthUnit_val k) z hz
  rw [Matrix.diagonal_map (map_zero _), hAd]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact Subalgebra.mem_center_iff.1 hz _

section CentralChat

variable {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
  {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}
  (hτ : Continuous τ) (hD : IsTypeDerivative τ D)

include hτ hD in
theorem Q_central {z : UU n} (hz : z ∈ Subalgebra.center ℂ (UU n)) (v : Fin d → ℂ)
    (i : Fin d) : Q τ z v i = xiPoly τ z * C (v i) := by
  obtain ⟨ξ, hξ⟩ := exists_Q_central hτ hD hz
  have hd : 0 < d := Fin.pos i
  have : xiPoly τ z = ξ := by
    rw [xiPoly, dite_eq_left hd, hξ]
    simp
  rw [hξ, this]

include hτ hD in
theorem xiPoly_top (hd : 0 < d) {z : UU n} {N : ℕ} (hzN : z ∈ degreeFiltration ℂ (LL n) N) :
    (xiPoly τ z).totalDegree ≤ N ∧
      homogeneousComponent N (xiPoly τ z) = diagRes n ((realSymbol n).symbol N z) := by
  have h := Q_degree hτ hD hzN (Pi.single ⟨0, hd⟩ 1)
  have hQ : Q τ z (Pi.single ⟨0, hd⟩ 1) ⟨0, hd⟩ = xiPoly τ z := by rw [xiPoly, dite_eq_left hd]
  refine ⟨hQ ▸ h.1 _, ?_⟩
  have h2 := h.2 ⟨0, hd⟩
  rw [hQ] at h2
  simpa using h2

include hτ hD in
/-- The degree-`l` part of the Gelfand polynomial is the power sum. -/
theorem xiPoly_Cgel_top (hd : 0 < d) (l : ℕ) :
    (xiPoly τ (Cgel n l)).totalDegree ≤ l ∧
      homogeneousComponent l (xiPoly τ (Cgel n l)) = psum (Fin n) ℂ l := by
  obtain ⟨h1, h2⟩ := xiPoly_top hτ hD hd (Cgel_mem_degreeFiltration (n := n) l)
  exact ⟨h1, h2.trans (diagRes_symbol_Cgel l)⟩

include hτ hD in
theorem Q_zero (v : Fin d → ℂ) : Q τ 0 v = 0 := Q_eq hτ hD (represents_zero v)

include hτ hD in
theorem chat_add (b b' : Matrix (Fin d) (Fin d) (UU n)) :
    chat τ (b + b') = chat τ b + chat τ b' := by
  ext m i
  simp only [chat, Matrix.of_apply, Matrix.add_apply, Q_add hτ hD, Pi.add_apply,
    Finset.sum_add_distrib]

include hτ hD in
theorem chat_diagonal_central {z : UU n} (hz : z ∈ Subalgebra.center ℂ (UU n)) :
    chat τ (Matrix.diagonal fun _ : Fin d => z) = Matrix.diagonal fun _ => xiPoly τ z := by
  refine Matrix.ext fun m i => ?_
  simp only [chat, Matrix.of_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, Q_central hτ hD hz]
    by_cases h : i = m
    · subst h; simp
    · simp [Ne.symm h]
  · intro j _ hji
    rw [ite_eq_right (Ne.symm hji), Q_zero hτ hD]
    rfl
  · simp

/-- Evaluation of polynomials at the Gelfand elements, in the center. -/
def zetaC (n : ℕ) : MvPolynomial ℕ ℂ →ₐ[ℂ] Subalgebra.center ℂ (UU n) :=
  aeval fun l => ⟨Cgel n l, Cgel_mem_center l⟩

/-- Evaluation of polynomials at the Gelfand elements. -/
def zeta (n : ℕ) (r : MvPolynomial ℕ ℂ) : UU n := (zetaC n r : UU n)

theorem zeta_mem_center (r : MvPolynomial ℕ ℂ) : zeta n r ∈ Subalgebra.center ℂ (UU n) :=
  (zetaC n r).2

theorem zeta_C (c : ℂ) : zeta n (C c) = algebraMap ℂ (UU n) c := by
  simp [zeta, zetaC]

theorem zeta_add (p q : MvPolynomial ℕ ℂ) : zeta n (p + q) = zeta n p + zeta n q := by
  simp [zeta]

theorem zeta_mul_X (p : MvPolynomial ℕ ℂ) (l : ℕ) : zeta n (p * X l) = zeta n p * Cgel n l := by
  simp [zeta, zetaC]

variable (τ) in
/-- Evaluation of polynomials at the Gelfand polynomials `ξ_l`. -/
def phiGel : MvPolynomial ℕ ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ := aeval fun l => xiPoly τ (Cgel n l)

include hτ hD in
theorem chat_diagonal_zeta (r : MvPolynomial ℕ ℂ) :
    chat τ (Matrix.diagonal fun _ : Fin d => zeta n r) = Matrix.diagonal fun _ => phiGel τ r := by
  induction r using MvPolynomial.induction_on with
  | C c =>
    rw [chat_diagonal_central hτ hD (zeta_mem_center _)]
    ext i j
    have hd : 0 < d := Fin.pos i
    simp only [Matrix.diagonal_apply]
    split_ifs
    · rw [phiGel, aeval_C, zeta_C, xiPoly, dite_eq_left hd, Algebra.algebraMap_eq_smul_one,
        Q_smul hτ hD, Q_one hτ hD]
      simp
    · rfl
  | add p q hp hq =>
    rw [zeta_add, map_add]
    have : (Matrix.diagonal fun _ : Fin d => zeta n p + zeta n q) =
        Matrix.diagonal (fun _ => zeta n p) + Matrix.diagonal fun _ => zeta n q :=
      (Matrix.diagonal_add _ _).symm
    rw [this, chat_add hτ hD, hp, hq, Matrix.diagonal_add]
  | mul_X p l hp =>
    have hdiag : (Matrix.diagonal fun _ : Fin d => zeta n (p * X l)) =
        Matrix.diagonal (fun _ => zeta n p) * Matrix.diagonal fun _ => Cgel n l := by
      rw [Matrix.diagonal_mul_diagonal, zeta_mul_X]
    rw [hdiag, chat_mul hτ hD _ (diagonal_mem_Bsub (Cgel_mem_center l)),
      chat_diagonal_central hτ hD (Cgel_mem_center l), hp, Matrix.diagonal_mul_diagonal,
      map_mul, phiGel, aeval_X, mul_comm]

end CentralChat

/-! ## Finiteness over the Gelfand polynomials -/

/-- The box exponents `β` with `β i < n`. -/
def boxSet (n : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.univ : Finset (Fin n → Fin n)).image
    fun f => Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)

theorem mem_boxSet {β : Fin n →₀ ℕ} (h : ∀ i, β i < n) : β ∈ boxSet n := by
  refine Finset.mem_image.2 ⟨fun i => ⟨β i, h i⟩, Finset.mem_univ _, ?_⟩
  ext i
  simp

/-- The polynomials `∑_{β ∈ box} φ(g_β) x^β`, `φ = aeval ξ`. -/
def SpanBox (ξ : ℕ → MvPolynomial (Fin n) ℂ) : Set (MvPolynomial (Fin n) ℂ) :=
  {f | ∃ g : (Fin n →₀ ℕ) → MvPolynomial ℕ ℂ, f = ∑ β ∈ boxSet n, aeval ξ (g β) * monomial β 1}

section SpanBox

variable {ξ : ℕ → MvPolynomial (Fin n) ℂ}

theorem SpanBox.zero : (0 : MvPolynomial (Fin n) ℂ) ∈ SpanBox ξ :=
  ⟨fun _ => 0, by simp⟩

theorem SpanBox.add {f f' : MvPolynomial (Fin n) ℂ} (h : f ∈ SpanBox ξ) (h' : f' ∈ SpanBox ξ) :
    f + f' ∈ SpanBox ξ := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  exact ⟨g + g', by simp [add_mul, Finset.sum_add_distrib]⟩

theorem SpanBox.mul_aeval (r : MvPolynomial ℕ ℂ) {f : MvPolynomial (Fin n) ℂ}
    (h : f ∈ SpanBox ξ) : aeval ξ r * f ∈ SpanBox ξ := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨fun β => r * g β, by simp [Finset.mul_sum, mul_assoc]⟩

theorem SpanBox.neg {f : MvPolynomial (Fin n) ℂ} (h : f ∈ SpanBox ξ) : -f ∈ SpanBox ξ := by
  have := SpanBox.mul_aeval (ξ := ξ) (-1) h
  simpa using this

theorem SpanBox.sub {f f' : MvPolynomial (Fin n) ℂ} (h : f ∈ SpanBox ξ) (h' : f' ∈ SpanBox ξ) :
    f - f' ∈ SpanBox ξ := by
  rw [sub_eq_add_neg]; exact SpanBox.add h (SpanBox.neg h')

theorem SpanBox.smul (c : ℂ) {f : MvPolynomial (Fin n) ℂ} (h : f ∈ SpanBox ξ) :
    c • f ∈ SpanBox ξ := by
  have := SpanBox.mul_aeval (ξ := ξ) (C c) h
  rwa [aeval_C, ← Algebra.smul_def] at this

theorem SpanBox.sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial (Fin n) ℂ}
    (h : ∀ i ∈ s, f i ∈ SpanBox ξ) : ∑ i ∈ s, f i ∈ SpanBox ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SpanBox.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact SpanBox.add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem SpanBox.monomial_box {β : Fin n →₀ ℕ} (hβ : β ∈ boxSet n) :
    monomial β (1 : ℂ) ∈ SpanBox ξ := by
  classical
  refine ⟨fun β' => if β' = β then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single β]
  · simp
  · intro β' _ hne; simp [hne]
  · intro h; exact absurd hβ h

end SpanBox

/-- `ξ - (degree-l part of ξ)` is the sum of the homogeneous components of degree `< l`. -/
theorem sub_homogeneousComponent_eq_sum {ξ : MvPolynomial (Fin n) ℂ} {l : ℕ}
    (hdeg : ξ.totalDegree ≤ l) :
    ξ - homogeneousComponent l ξ = ∑ k ∈ Finset.range l, homogeneousComponent k ξ := by
  have h : ∑ k ∈ Finset.range (l + 1), homogeneousComponent k ξ = ξ := by
    conv_rhs => rw [← sum_homogeneousComponent ξ]
    refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hk hk' => ?_).symm
    simp only [Finset.mem_range] at hk hk'
    exact homogeneousComponent_eq_zero k ξ (by omega)
  have h2 : ξ = ∑ k ∈ Finset.range l, homogeneousComponent k ξ + homogeneousComponent l ξ := by
    rw [← Finset.sum_range_succ, h]
  nth_rewrite 1 [h2]
  rw [add_sub_cancel_right]

/-- **Finiteness.** If `ξ_l` has degree `≤ l` and degree-`l` part `p_l` for `l ≥ 1`, then every
polynomial is a combination of the box monomials with coefficients polynomial in the `ξ_l`. -/
theorem mem_spanBox {ξ : ℕ → MvPolynomial (Fin n) ℂ}
    (hξ : ∀ l, 1 ≤ l → (ξ l).totalDegree ≤ l ∧ homogeneousComponent l (ξ l) = psum (Fin n) ℂ l)
    (f : MvPolynomial (Fin n) ℂ) : f ∈ SpanBox ξ := by
  classical
  suffices key : ∀ D, ∀ f : MvPolynomial (Fin n) ℂ, f.totalDegree < D → f ∈ SpanBox ξ from
    key _ f (Nat.lt_succ_self _)
  intro D
  induction D with
  | zero => intro f hf; exact absurd hf (Nat.not_lt_zero _)
  | succ D ih =>
    intro f hf
    have hmon : ∀ α : Fin n →₀ ℕ, α.degree ≤ D → monomial α (1 : ℂ) ∈ SpanBox ξ := by
      intro α hα
      rcases hα.lt_or_eq with hlt | heq
      · exact ih _ (lt_of_le_of_lt ((isHomogeneous_monomial (1 : ℂ) rfl).totalDegree_le) hlt)
      by_cases hbox : ∀ i, α i < n
      · exact SpanBox.monomial_box (mem_boxSet hbox)
      push Not at hbox
      obtain ⟨i, hi⟩ := hbox
      have hps := RealJacquetFiniteGeneration.monomial_mem_powerSumSpan (n := n) hi
      rw [heq] at hps
      refine Submodule.span_induction (p := fun x _ => x ∈ SpanBox ξ) (fun p hp => ?_)
        SpanBox.zero (fun p q _ _ hp hq => SpanBox.add hp hq) (fun c p _ hp => SpanBox.smul c hp) hps
      · obtain ⟨γ, l, hl, hdeg, rfl⟩ := hp
        obtain ⟨hξ1, hξ2⟩ := hξ l hl
        have hpsum : psum (Fin n) ℂ l = ξ l - ∑ k ∈ Finset.range l, homogeneousComponent k (ξ l) := by
          rw [← sub_homogeneousComponent_eq_sum hξ1, hξ2, sub_sub_cancel]
        have hγ : monomial γ (1 : ℂ) ∈ SpanBox ξ :=
          ih _ (lt_of_le_of_lt ((isHomogeneous_monomial (1 : ℂ) rfl).totalDegree_le) (by omega))
        rw [hpsum, mul_sub, Finset.mul_sum]
        refine SpanBox.sub ?_ (SpanBox.sum _ fun k hk => ih _ ?_)
        · have := SpanBox.mul_aeval (ξ := ξ) (X l) hγ
          rwa [aeval_X, mul_comm] at this
        · simp only [Finset.mem_range] at hk
          refine lt_of_le_of_lt (((isHomogeneous_monomial (1 : ℂ) rfl).mul
            (homogeneousComponent_isHomogeneous k (ξ l))).totalDegree_le) ?_
          omega
    rw [as_sum f]
    refine SpanBox.sum _ fun α hα => ?_
    rw [show monomial α (f.coeff α) = f.coeff α • monomial α (1 : ℂ) by
      rw [smul_monomial, smul_eq_mul, mul_one]]
    refine SpanBox.smul _ (hmon α ?_)
    have := le_totalDegree hα
    have h2 : α.degree = α.sum fun _ e => e := by
      rw [Finsupp.degree_eq_sum, Finsupp.sum_fintype _ _ (fun _ => rfl)]
    omega

/-! ## The fibre of the Gelfand polynomials is finite -/

theorem eval_aeval_of_fibre {ξ : ℕ → MvPolynomial (Fin n) ℂ} {lam : ℕ → ℂ} {a : Fin n → ℂ}
    (ha : ∀ l, eval a (ξ l) = lam l) (r : MvPolynomial ℕ ℂ) :
    eval a (aeval ξ r) = eval lam r := by
  induction r using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p l hp => rw [map_mul, map_mul, hp, aeval_X, ha l, map_mul, eval_X]

/-- **The fibre is finite.** Only finitely many `a` satisfy `ξ_l(a) = λ_l` for all `l`. -/
theorem finite_fibre {ξ : ℕ → MvPolynomial (Fin n) ℂ}
    (hξ : ∀ l, 1 ≤ l → (ξ l).totalDegree ≤ l ∧ homogeneousComponent l (ξ l) = psum (Fin n) ℂ l)
    (lam : ℕ → ℂ) : {a : Fin n → ℂ | ∀ l, eval a (ξ l) = lam l}.Finite := by
  classical
  set K := (boxSet n).card + 1
  have hroot : ∀ i : Fin n, ∃ P : Polynomial ℂ, P ≠ 0 ∧
      ∀ a : Fin n → ℂ, (∀ l, eval a (ξ l) = lam l) → P.IsRoot (a i) := by
    intro i
    choose g hg using fun k : Fin K => mem_spanBox hξ ((X i : MvPolynomial (Fin n) ℂ) ^ (k : ℕ))
    let v : Fin K → (boxSet n → ℂ) := fun k β => eval lam (g k β)
    have hnot : ¬ LinearIndependent ℂ v := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp [K, Module.finrank_fintype_fun_eq_card] at this
    obtain ⟨t, ht, k0, hk0⟩ := Fintype.not_linearIndependent_iff.1 hnot
    refine ⟨∑ k : Fin K, Polynomial.C (t k) * Polynomial.X ^ (k : ℕ), ?_, ?_⟩
    · intro h0
      apply hk0
      have := congrArg (fun P : Polynomial ℂ => P.coeff (k0 : ℕ)) h0
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single k0 (fun k _ hk => by
        rw [ite_eq_right (fun h => hk (Fin.ext h).symm)]) (by simp)] at this
      simpa using this
    · intro a ha
      have hk : ∀ k : Fin K, a i ^ (k : ℕ) = ∑ β ∈ boxSet n, eval lam (g k β) *
          eval a (monomial β (1 : ℂ)) := by
        intro k
        have := congrArg (eval a) (hg k)
        rw [map_pow, eval_X, map_sum] at this
        rw [this]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [map_mul, eval_aeval_of_fibre ha]
      simp only [Polynomial.IsRoot, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hk, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hβ : ∀ β : boxSet n, ∑ k : Fin K, t k * v k β = 0 := by
        intro β
        have := congrFun ht β
        simpa [Finset.sum_apply] using this
      rw [← Finset.sum_coe_sort (boxSet n)]
      refine Finset.sum_eq_zero fun β _ => ?_
      have := hβ β
      simp only [v] at this
      simp only [← mul_assoc]
      rw [← Finset.sum_mul, this, zero_mul]
  choose P hP0 hProot using hroot
  refine (Set.Finite.pi' fun i => Polynomial.finite_setOfPred_isRoot (hP0 i)).subset ?_
  intro a ha i
  exact hProot i a ha

/-! ## The determinant trick -/

/-- **Determinant trick** (Cayley–Hamilton for finite modules) for left multiplication by a
matrix `Y` with entries in `J A`, `A` a finite `R`-algebra: `∑ₖ pₖ Yᵏ = 0` for a monic `p` with
`pₖ ∈ J^(deg p - k)`. -/
theorem exists_monic_matrix_poly {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] {d : ℕ} (J : Ideal R) (Y : Matrix (Fin d) (Fin d) A)
    (hY : ∀ i j, Y i j ∈ Ideal.map (algebraMap R A) J) :
    ∃ p : Polynomial R, p.Monic ∧ (∀ k, p.coeff k ∈ J ^ (p.natDegree - k)) ∧
      ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap R A (p.coeff k) • Y ^ k = 0 := by
  classical
  have : Module.Finite R (Matrix (Fin d) (Fin d) A) :=
    Module.Finite.equiv (Matrix.ofLinearEquiv R)
  let f : Module.End R (Matrix (Fin d) (Fin d) A) :=
    { toFun := fun X => Y * X
      map_add' := Matrix.mul_add Y
      map_smul' := fun r X => Matrix.mul_smul Y r X }
  have hf : ∀ X, f X = Y * X := fun X => rfl
  have hsmul : ∀ y ∈ Ideal.map (algebraMap R A) J, ∀ B : Matrix (Fin d) (Fin d) A,
      y • B ∈ J • (⊤ : Submodule R (Matrix (Fin d) (Fin d) A)) := by
    intro y hy
    have hy' : y ∈ Ideal.span (algebraMap R A '' J) := hy
    refine Submodule.span_induction (p := fun y _ => ∀ B : Matrix (Fin d) (Fin d) A,
      y • B ∈ J • (⊤ : Submodule R (Matrix (Fin d) (Fin d) A))) ?_ ?_ ?_ ?_ hy'
    · rintro _ ⟨j, hj, rfl⟩ B
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hj trivial
    · intro B; rw [zero_smul]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy B; rw [add_smul]; exact Submodule.add_mem _ (hx B) (hy B)
    · intro c x _ hx B; rw [smul_eq_mul, mul_comm, mul_smul]; exact hx _
  have hrange : LinearMap.range f ≤ J • ⊤ := by
    rintro _ ⟨X, rfl⟩
    rw [hf]
    have hYdec : Y = ∑ i, ∑ j, Y i j • Matrix.single i j (1 : A) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hYdec, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_mul_assoc]
    exact hsmul _ (hY i j) _
  obtain ⟨p, hmon, -, hcoeff, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R f J hrange
  refine ⟨p, hmon, hcoeff, ?_⟩
  have hpow : ∀ k : ℕ, (f ^ k) 1 = Y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hf, pow_succ']
  have h1 := LinearMap.congr_fun hp 1
  rw [Polynomial.aeval_eq_sum_range, LinearMap.zero_apply, LinearMap.sum_apply] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, hpow, algebraMap_smul]

/-! ## Matrices acting through central elements -/

section ActLemmas

variable {d : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (P : UU n →ₐ[ℂ] Module.End ℂ M)

theorem act_add (b b' : Matrix (Fin d) (Fin d) (UU n)) (T : (Fin d → ℂ) →ₗ[ℂ] M) :
    act P (b + b') T = act P b T + act P b' T := by
  refine LinearMap.pi_ext fun i c => ?_
  simp [act_single, Finset.sum_add_distrib, smul_add]

theorem act_zero' (T : (Fin d → ℂ) →ₗ[ℂ] M) : act P (0 : Matrix (Fin d) (Fin d) (UU n)) T = 0 := by
  refine LinearMap.pi_ext fun i c => ?_
  simp [act_single]

theorem act_sum {ι : Type*} (s : Finset ι) (b : ι → Matrix (Fin d) (Fin d) (UU n))
    (T : (Fin d → ℂ) →ₗ[ℂ] M) : act P (∑ k ∈ s, b k) T = ∑ k ∈ s, act P (b k) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [act_zero']
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, act_add, ih]

theorem act_diagonal (z : UU n) (T : (Fin d → ℂ) →ₗ[ℂ] M) :
    act P (Matrix.diagonal fun _ => z) T = P z ∘ₗ T := by
  classical
  refine LinearMap.pi_ext fun i c => ?_
  rw [act_single, LinearMap.comp_apply, Finset.sum_eq_single i (fun j _ hj => by
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]) (by simp)]
  rw [Matrix.diagonal_apply_eq, ← map_smul (P z), ← map_smul T c (Pi.single i 1),
    ← Pi.single_smul, smul_eq_mul, mul_one]

end ActLemmas

/-! ## Nilpotency -/

section Nilpotent

variable {d : ℕ} {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
  {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ}
  (hτ : Continuous τ) (hD : IsTypeDerivative τ D)

include hτ hD in
theorem chat_one : chat τ (1 : Matrix (Fin d) (Fin d) (UU n)) = 1 := by
  have h := chat_diagonal_zeta hτ hD (n := n) (d := d) (C 1)
  rw [zeta_C] at h
  simp only [map_one, Matrix.diagonal_one] at h
  exact h

include hτ hD in
theorem chat_pow {x : Matrix (Fin d) (Fin d) (UU n)} (hx : x ∈ Bsub τ) (k : ℕ) :
    chat τ (x ^ k) = chat τ x ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, chat_one hτ hD]
  | succ k ih => rw [pow_succ, chat_mul hτ hD _ hx, ih, pow_succ']

include hτ hD in
theorem chat_sum {ι : Type*} (s : Finset ι) (b : ι → Matrix (Fin d) (Fin d) (UU n)) :
    chat τ (∑ k ∈ s, b k) = ∑ k ∈ s, chat τ (b k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine Matrix.ext fun m i => ?_
    simp [chat, Q_zero hτ hD]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, chat_add hτ hD, ih]

theorem entries_pow_mem {R : Type*} [CommRing R] {I : Ideal R} {A : Matrix (Fin d) (Fin d) R}
    (hA : ∀ i j, A i j ∈ I) : ∀ (k : ℕ) (i j : Fin d), (A ^ k) i j ∈ I ^ k := by
  intro k
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    rw [pow_succ A k, Matrix.mul_apply, pow_succ I k]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_mul (ih i m) (hA m j)

include hτ hD in
/-- **Nilpotency.** Suppose the Gelfand elements act on the `(𝔤𝔩_n(ℝ), O(n))`-module `M` by the
scalars `λ_l`, and let `x` be `K`-invariant with `ĉ(x)(a) = 0` at every `a` of the fibre
`{a : ξ_l(a) = λ_l}`. Then a power of `x` kills every `K`-intertwiner `T₀` from `τ` into `M`. -/
theorem exists_pow_act_eq_zero (hd : 0 < d) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) M}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ M} (hgk : IsRealGKModule n ρ π)
    (lam : ℕ → ℂ) (hlam : ∀ l, envelopingAction π (Cgel n l) = algebraMap ℂ _ (lam l))
    {T0 : (Fin d → ℂ) →ₗ[ℂ] M} (hT0 : T0 ∈ gkIntertwiners ρ d τ)
    {x : Matrix (Fin d) (Fin d) (UU n)} (hx : x ∈ Bsub τ)
    (hZ : ∀ a : Fin n → ℂ, (∀ l, eval a (xiPoly τ (Cgel n l)) = lam l) →
      (chat τ x).map (eval a) = 0) :
    ∃ m, act (envelopingAction π) (x ^ m) T0 = 0 := by
  classical
  set ξ : ℕ → MvPolynomial (Fin n) ℂ := fun l => xiPoly τ (Cgel n l) with hξdef
  have hξ : ∀ l, 1 ≤ l → (ξ l).totalDegree ≤ l ∧
      homogeneousComponent l (ξ l) = psum (Fin n) ℂ l :=
    fun l _ => xiPoly_Cgel_top hτ hD hd l
  set I : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span (Set.range fun l => ξ l - C (lam l))
  have hrad : ∀ i j, chat τ x i j ∈ I.radical := by
    intro i j
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro a ha
    rw [MvPolynomial.mem_zeroLocus_iff] at ha
    have hfib : ∀ l, eval a (ξ l) = lam l := by
      intro l
      have := ha _ (Ideal.subset_span ⟨l, rfl⟩)
      rw [map_sub, aeval_C, sub_eq_zero] at this
      simpa using this
    have := congrFun (congrFun (hZ a hfib) i) j
    simpa using this
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg I (IsNoetherian.noetherian _)
  set Y := chat τ x ^ N
  have hY : ∀ i j, Y i j ∈ I := fun i j => hN (entries_pow_mem hrad N i j)
  let _ : Algebra (MvPolynomial ℕ ℂ) (MvPolynomial (Fin n) ℂ) := (phiGel τ).toRingHom.toAlgebra
  have halg : ∀ r, algebraMap (MvPolynomial ℕ ℂ) (MvPolynomial (Fin n) ℂ) r = phiGel τ r :=
    fun r => rfl
  have : Module.Finite (MvPolynomial ℕ ℂ) (MvPolynomial (Fin n) ℂ) := by
    refine ⟨⟨(boxSet n).image fun β => monomial β (1 : ℂ), ?_⟩⟩
    rw [eq_top_iff]
    rintro f -
    obtain ⟨g, rfl⟩ := mem_spanBox hξ f
    refine Submodule.sum_mem _ fun β hβ => ?_
    have : aeval ξ (g β) * monomial β (1 : ℂ) = g β • monomial β (1 : ℂ) := by
      rw [Algebra.smul_def, halg]; rfl
    rw [this]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hβ)))
  set J : Ideal (MvPolynomial ℕ ℂ) := RingHom.ker (eval lam)
  have hIJ : I ≤ Ideal.map (algebraMap (MvPolynomial ℕ ℂ) (MvPolynomial (Fin n) ℂ)) J := by
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    show ξ l - C (lam l) ∈ _
    have : ξ l - C (lam l) =
        algebraMap (MvPolynomial ℕ ℂ) (MvPolynomial (Fin n) ℂ) (X l - C (lam l)) := by
      rw [halg, map_sub, phiGel, aeval_X, aeval_C]
      rfl
    rw [this]
    exact Ideal.mem_map_of_mem _ (by simp [J])
  obtain ⟨p, hmon, hcoeff, hpY⟩ := exists_monic_matrix_poly J Y fun i j => hIJ (hY i j)
  set w : Matrix (Fin d) (Fin d) (UU n) := ∑ k ∈ Finset.range (p.natDegree + 1),
    Matrix.diagonal (fun _ => zeta n (p.coeff k)) * x ^ (N * k)
  have hw : w ∈ Bsub τ := Subalgebra.sum_mem _ fun k _ =>
    Subalgebra.mul_mem _ (diagonal_mem_Bsub (zeta_mem_center _)) (Subalgebra.pow_mem _ hx _)
  have hchat : chat τ w = 0 := by
    rw [chat_sum hτ hD, ← hpY]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [chat_mul hτ hD _ (Subalgebra.pow_mem _ hx _), chat_pow hτ hD hx,
      chat_diagonal_zeta hτ hD, pow_mul, halg, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  have hact := act_eq_zero_of_chat_eq_zero hτ hD hw hchat hgk hT0
  have hzeta : ∀ r, envelopingAction π (zeta n r) = algebraMap ℂ _ (eval lam r) := by
    have h : (envelopingAction π).comp ((Subalgebra.val _).comp (zetaC n)) =
        (Algebra.ofId ℂ (Module.End ℂ M)).comp (aeval lam) := by
      refine MvPolynomial.algHom_ext fun l => ?_
      simp [zetaC, hlam]
    intro r
    have := congrArg (fun f => f r) h
    simpa [zeta] using this
  refine ⟨N * p.natDegree, ?_⟩
  rw [act_sum, Finset.sum_range_succ] at hact
  have hrest : ∑ k ∈ Finset.range p.natDegree, act (envelopingAction π)
      (Matrix.diagonal (fun _ => zeta n (p.coeff k)) * x ^ (N * k)) T0 = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hJ : p.coeff k ∈ J := Ideal.pow_le_self (by omega) (hcoeff k)
    have h0 : eval lam (p.coeff k) = 0 := hJ
    rw [act_mul, act_diagonal, hzeta, h0, map_zero, LinearMap.zero_comp]
  rw [hrest, zero_add, act_mul, act_diagonal, hzeta, hmon.coeff_natDegree, map_one, map_one,
    Module.End.one_eq_id, LinearMap.id_comp] at hact
  exact hact

end Nilpotent

end RealSubquotient

end Langlands.Archimedean
