import Langlands.Representation.Archimedean.ComplexJacquetReduction
import Langlands.Representation.Archimedean.ComplexGenericLargeReduction
import Langlands.Representation.Archimedean.Kostant.Center
import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Jacquet module of an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module is finite-dimensional

For an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` on `V` and `𝔫V` the span of the
vectors `π(1 ⊗ X) v`, `X` strictly upper triangular, `V/𝔫V` is finite-dimensional
(`ComplexJacquetModuleFiniteDimensionalStatement`, proved by
`complexJacquetModuleFiniteDimensional`). With the nonvanishing statement
`ComplexJacquetModuleNonzeroStatement` it gives the Library's
`ComplexJacquetModuleFiniteStatement` (`complexJacquetModuleFinite_of_nonzero`).

Write `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` (`ComplexGenericLarge.prodAction`) and let `E^{(i)}`
be the matrix of the operators `E^{(i)}_{pq}` of the factor `i` (`ee`). The proof has four steps.

* **Gelfand's recursion modulo `N`** (`diag_pow`): for every subspace `N` containing the images
  of the strictly upper `E_ab` and stable under the diagonal `E_aa`, the diagonal entries of
  `E^k` act modulo `N` as explicit polynomials `g_k(a)` in the diagonal, with leading term
  `E_aa^k` (`gelPoly`, `totalDegree_gelPoly_sub`).
* **Infinitesimal character** (`trace_scalar`): `tr E^k` is central (`Kostant.gel_mem_center`)
  and acts by a scalar (`ComplexGenericLarge.prodAction_hasInfinitesimalCharacter`). Hence the
  power sums of the diagonal generators are congruent to lower-degree polynomials modulo the
  ideal of polynomials acting into `𝔫V`; Newton's identities then give a relation of degree `n`
  for each diagonal generator (`xpow_rel`), and every polynomial reduces to monomials of
  exponents `< n` (`mem_boxSpan_sup`).
* **Spanning** (`diagSpan_sup_eq_top`): `W`, the `U(n)`-span of a nonzero vector, is
  finite-dimensional and stable under `𝔲(n)` (`skew_stable`, along `t ↦ exp(tY)`). Every matrix is
  skew-Hermitian plus upper triangular, so the upper triangular closure of `W` is stable under
  `π`, hence everything by irreducibility; and `𝔫V` plus the span of the vectors `p(𝔥) w`,
  `w ∈ W`, is stable under the upper triangular directions.
* Together, `V/𝔫V` is the image of the finite-dimensional space spanned by the box monomials
  applied to `W`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexJacquetFinite

open MvPolynomial

/-! ## Gelfand's recursion modulo a subspace -/

section Recursion

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- The commutation relations `[e_ab, e_cd] = δ_bc e_ad - δ_da e_cb` of the matrix units of
`𝔤𝔩_n`. -/
def IsGlFamily (e : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b c d, e a b * e c d - e c d * e a b =
    (if b = c then e a d else 0) - (if d = a then e c b else 0)

variable {e : Fin n → Fin n → Module.End ℂ V}

theorem pow_succ_apply (k : ℕ) (x y : Fin n) :
    (Matrix.of e ^ (k + 1)) x y = ∑ z, e x z * (Matrix.of e ^ k) z y := by
  rw [pow_succ', Matrix.mul_apply]
  rfl

/-- `[e_ac, (E^k)_xy] = δ_xc (E^k)_ay - δ_ay (E^k)_xc`. -/
theorem comm_pow (he : IsGlFamily e) (k : ℕ) (a c x y : Fin n) :
    e a c * (Matrix.of e ^ k) x y - (Matrix.of e ^ k) x y * e a c =
      (if x = c then (Matrix.of e ^ k) a y else 0) -
        (if a = y then (Matrix.of e ^ k) x c else 0) := by
  induction k generalizing x y with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    by_cases hxy : x = y <;> by_cases hxc : x = c <;> by_cases hay : a = y <;>
      simp_all
  | succ k ih =>
    rw [pow_succ_apply, pow_succ_apply, pow_succ_apply, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    have hz : ∀ z, e a c * (e x z * (Matrix.of e ^ k) z y) -
        e x z * (Matrix.of e ^ k) z y * e a c =
          (e a c * e x z - e x z * e a c) * (Matrix.of e ^ k) z y +
            e x z * (e a c * (Matrix.of e ^ k) z y - (Matrix.of e ^ k) z y * e a c) := by
      intro z; noncomm_ring
    simp_rw [hz, he a c x, ih]
    simp only [sub_mul, mul_sub, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hxc : x = c
    · subst hxc
      by_cases hay : a = y
      · subst hay; simp
      · simp [hay]
    · have hcx : ¬c = x := fun h => hxc h.symm
      by_cases hay : a = y
      · subst hay; simp [hxc, hcx]; abel
      · simp [hxc, hcx, hay]

variable (N : Submodule ℂ V)

/-- The entries `(E^k)_cb`, `c < b`, map `V` into `N`. -/
theorem upper_pow (he : IsGlFamily e) (hup : ∀ a b : Fin n, a < b → ∀ v, e a b v ∈ N)
    (hdiag : ∀ a, ∀ v ∈ N, e a a v ∈ N) :
    ∀ (k : ℕ) (c b : Fin n), c < b → ∀ v, (Matrix.of e ^ k) c b v ∈ N := by
  intro k
  induction k with
  | zero =>
    intro c b hcb v
    simp [Matrix.one_apply_ne hcb.ne]
  | succ k ih =>
    intro c b hcb v
    rw [pow_succ_apply, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [Module.End.mul_apply]
    rcases lt_trichotomy d c with hdc | rfl | hcd
    · have h := LinearMap.congr_fun (comm_pow he k c d d b) v
      simp only [hcb.ne, ↓reduceIte, LinearMap.sub_apply, Module.End.mul_apply,
        sub_zero] at h
      have h' : e c d ((Matrix.of e ^ k) d b v) =
          (Matrix.of e ^ k) d b (e c d v) + (Matrix.of e ^ k) c b v := by
        rw [← h]; abel
      rw [h']
      exact N.add_mem (ih d b (hdc.trans hcb) _) (ih c b hcb v)
    · exact hdiag d _ (ih d b hcb v)
    · exact hup c d hcd _

/-- The polynomials of Gelfand's recursion: `g_0(a) = 1` and
`g_{k+1}(a) = (X_a + a) g_k(a) - ∑_{c < a} g_k(c)`. -/
def gelPoly (n : ℕ) : ℕ → Fin n → MvPolynomial (Fin n) ℂ
  | 0, _ => 1
  | k + 1, a => (X a + C ((a : ℕ) : ℂ)) * gelPoly n k a - ∑ c ∈ Finset.Iio a, gelPoly n k c

theorem gelPoly_zero (a : Fin n) : gelPoly n 0 a = 1 := rfl

theorem gelPoly_succ (k : ℕ) (a : Fin n) :
    gelPoly n (k + 1) a =
      (X a + C ((a : ℕ) : ℂ)) * gelPoly n k a - ∑ c ∈ Finset.Iio a, gelPoly n k c := rfl

/-- **Gelfand's recursion modulo `N`.** If `ψ` sends `X_a` to `e_aa`, then
`(E^k)_aa v ≡ ψ(g_k(a)) v` modulo `N`. -/
theorem diag_pow (he : IsGlFamily e) (hup : ∀ a b : Fin n, a < b → ∀ v, e a b v ∈ N)
    (hdiag : ∀ a, ∀ v ∈ N, e a a v ∈ N)
    (ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ V) (hψ : ∀ a, ψ (X a) = e a a) :
    ∀ (k : ℕ) (a : Fin n) (v : V), (Matrix.of e ^ k) a a v - ψ (gelPoly n k a) v ∈ N := by
  intro k
  induction k with
  | zero =>
    intro a v
    simp [gelPoly_zero]
  | succ k ih =>
    intro a v
    set f : Fin n → V := fun c => if c < a then ψ (gelPoly n k a) v - ψ (gelPoly n k c) v
      else if c = a then e a a (ψ (gelPoly n k a) v) else 0 with hf
    have hψg : ψ (gelPoly n (k + 1) a) v = ∑ c, f c := by
      rw [Finset.sum_ite, Finset.sum_ite_eq']
      · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio,
          gelPoly_succ, map_sub, map_mul, map_add, hψ, map_sum, LinearMap.sub_apply,
          Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply,
          MvPolynomial.algHom_C, Module.algebraMap_end_apply, ← Nat.cast_smul_eq_nsmul ℂ]
        have ha : a ∈ Finset.univ.filter (fun x => ¬x < a) := by simp
        simp only [ha, ↓reduceIte]
        abel
    rw [pow_succ_apply, LinearMap.sum_apply, hψg, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [Module.End.mul_apply]
    rcases lt_trichotomy c a with hca | rfl | hac
    · simp only [hf, hca, ↓reduceIte]
      have h := LinearMap.congr_fun (comm_pow he k a c c a) v
      simp only [↓reduceIte, LinearMap.sub_apply, Module.End.mul_apply] at h
      have h' : e a c ((Matrix.of e ^ k) c a v) =
          (Matrix.of e ^ k) c a (e a c v) + ((Matrix.of e ^ k) a a v - (Matrix.of e ^ k) c c v) := by
        rw [← h]; abel
      rw [h']
      have h1 := upper_pow N he hup hdiag k c a hca (e a c v)
      convert N.add_mem h1 (N.sub_mem (ih a v) (ih c v)) using 1
      abel
    · simp only [hf, lt_irrefl, ↓reduceIte]
      rw [← map_sub]
      exact hdiag c _ (ih c v)
    · simp only [hf, not_lt.2 hac.le, hac.ne', ↓reduceIte, sub_zero]
      exact hup a c hac _

/-- `g_k(a)` has total degree at most `k`. -/
theorem totalDegree_gelPoly : ∀ (k : ℕ) (a : Fin n), (gelPoly n k a).totalDegree ≤ k
  | 0, a => by simp [gelPoly_zero]
  | k + 1, a => by
    rw [gelPoly_succ]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      have h1 : (X a + C ((a : ℕ) : ℂ) : MvPolynomial (Fin n) ℂ).totalDegree ≤ 1 :=
        (totalDegree_add _ _).trans (max_le (totalDegree_X _).le ((totalDegree_C _).trans_le (Nat.zero_le 1)))
      have h2 := totalDegree_gelPoly k a
      omega
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
      exact (totalDegree_gelPoly k c).trans (Nat.le_succ k)

/-- The leading term of `g_{k+1}(a)` is `X_a^{k+1}`. -/
theorem totalDegree_gelPoly_sub :
    ∀ (k : ℕ) (a : Fin n), (gelPoly n (k + 1) a - X a ^ (k + 1)).totalDegree ≤ k
  | 0, a => by
    have h : gelPoly n 1 a - X a ^ 1 =
        C ((a : ℕ) : ℂ) - ∑ c ∈ Finset.Iio a, (1 : MvPolynomial (Fin n) ℂ) := by
      rw [gelPoly_succ]
      simp only [gelPoly_zero, mul_one, pow_one]
      ring
    rw [h]
    refine (totalDegree_sub _ _).trans (max_le (totalDegree_C _).le ?_)
    exact (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => by simp)
  | k + 1, a => by
    have h : gelPoly n (k + 2) a - X a ^ (k + 2) =
        X a * (gelPoly n (k + 1) a - X a ^ (k + 1)) +
          (C ((a : ℕ) : ℂ) * gelPoly n (k + 1) a -
            ∑ c ∈ Finset.Iio a, gelPoly n (k + 1) c) := by
      rw [gelPoly_succ (k + 1)]
      ring
    rw [h]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_gelPoly_sub k a
      rw [totalDegree_X]
      omega
    · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        exact totalDegree_gelPoly (k + 1) a
      · exact (totalDegree_finsetSum _ _).trans
          (Finset.sup_le fun c _ => totalDegree_gelPoly (k + 1) c)

end Recursion

/-! ## Reduction of monomials modulo an ideal with power-sum relations -/

section Close

variable {σ : Type*}

/-- `f` is congruent modulo `I` to a polynomial of total degree at most `d`. -/
def Close (I : Ideal (MvPolynomial σ ℂ)) (f : MvPolynomial σ ℂ) (d : ℕ) : Prop :=
  ∃ r : MvPolynomial σ ℂ, r.totalDegree ≤ d ∧ f - r ∈ I

variable {I : Ideal (MvPolynomial σ ℂ)}

theorem close_of_totalDegree_le {f : MvPolynomial σ ℂ} {d : ℕ} (h : f.totalDegree ≤ d) :
    Close I f d :=
  ⟨f, h, by simp⟩

theorem Close.mono {f : MvPolynomial σ ℂ} {d d' : ℕ} (h : Close I f d) (hd : d ≤ d') :
    Close I f d' :=
  let ⟨r, hr, hm⟩ := h
  ⟨r, hr.trans hd, hm⟩

theorem Close.add {f g : MvPolynomial σ ℂ} {d : ℕ} (hf : Close I f d) (hg : Close I g d) :
    Close I (f + g) d := by
  obtain ⟨r, hr, hfr⟩ := hf
  obtain ⟨s, hs, hgs⟩ := hg
  refine ⟨r + s, (totalDegree_add _ _).trans (max_le hr hs), ?_⟩
  convert I.add_mem hfr hgs using 1
  ring

theorem Close.neg {f : MvPolynomial σ ℂ} {d : ℕ} (hf : Close I f d) : Close I (-f) d := by
  obtain ⟨r, hr, hfr⟩ := hf
  refine ⟨-r, by rwa [totalDegree_neg], ?_⟩
  convert I.neg_mem hfr using 1
  ring

theorem Close.mul {f g : MvPolynomial σ ℂ} {d d' : ℕ} (hf : Close I f d) (hg : Close I g d') :
    Close I (f * g) (d + d') := by
  obtain ⟨r, hr, hfr⟩ := hf
  obtain ⟨s, hs, hgs⟩ := hg
  refine ⟨r * s, (totalDegree_mul _ _).trans (add_le_add hr hs), ?_⟩
  have h : f * g - r * s = (f - r) * g + r * (g - s) := by ring
  rw [h]
  exact I.add_mem (I.mul_mem_right _ hfr) (I.mul_mem_left _ hgs)

theorem close_sum {ι : Type*} (t : Finset ι) {f : ι → MvPolynomial σ ℂ} {d : ℕ}
    (h : ∀ i ∈ t, Close I (f i) d) : Close I (∑ i ∈ t, f i) d :=
  Finset.sum_induction f (fun g => Close I g d) (fun _ _ ha hb => ha.add hb)
    (close_of_totalDegree_le (by simp)) h

theorem close_const_mul {f : MvPolynomial σ ℂ} {d : ℕ} (c : ℂ) (hf : Close I f d) :
    Close I (C c * f) d := by
  simpa using (close_of_totalDegree_le (I := I) (totalDegree_C c).le).mul hf

theorem close_neg_one_pow (m d : ℕ) : Close I ((-1 : MvPolynomial σ ℂ) ^ m) d := by
  refine close_of_totalDegree_le ((totalDegree_pow _ _).trans ?_)
  simp [totalDegree_neg]

theorem Close.rename {τ : Type*} {J : Ideal (MvPolynomial τ ℂ)} (g : σ → τ)
    {f : MvPolynomial σ ℂ} {d : ℕ} (h : Close (J.comap (MvPolynomial.rename (R := ℂ) g)) f d) :
    Close J (MvPolynomial.rename g f) d := by
  obtain ⟨r, hr, hm⟩ := h
  refine ⟨MvPolynomial.rename g r, (totalDegree_rename_le g r).trans hr, ?_⟩
  rw [← map_sub]
  exact hm

end Close

section Newton

variable {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}

/-- If every power sum `p_b`, `1 ≤ b ≤ n`, is congruent modulo `I` to a polynomial of degree
`< b`, so is every elementary symmetric polynomial `e_k`, `1 ≤ k ≤ n` (Newton's identities). -/
theorem esymm_close (hp : ∀ b, 1 ≤ b → b ≤ n → Close I (psum (Fin n) ℂ b) (b - 1)) :
    ∀ k, 1 ≤ k → k ≤ n → Close I (esymm (Fin n) ℂ k) (k - 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk1 hkn
  have hsum : Close I (∑ a ∈ Finset.antidiagonal k with a.1 < k,
      (-1 : MvPolynomial (Fin n) ℂ) ^ a.1 * esymm (Fin n) ℂ a.1 * psum (Fin n) ℂ a.2) (k - 1) := by
    refine close_sum _ fun a ha => ?_
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    obtain ⟨hak, hlt⟩ := ha
    have hps : Close I (psum (Fin n) ℂ a.2) (a.2 - 1) := hp a.2 (by omega) (by omega)
    by_cases ha0 : a.1 = 0
    · rw [ha0, esymm_zero, pow_zero, one_mul, one_mul]
      exact hps.mono (by omega)
    · have hes : Close I (esymm (Fin n) ℂ a.1) (a.1 - 1) :=
        ih a.1 hlt (by omega) (by omega)
      exact (((close_neg_one_pow a.1 0).mul hes).mul hps).mono (by omega)
  have hk : Close I ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) (k - 1) := by
    rw [mul_esymm_eq_sum]
    exact ((close_neg_one_pow (k + 1) 0).mul hsum).mono (by omega)
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have heq : esymm (Fin n) ℂ k = C (k : ℂ)⁻¹ * ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) := by
    rw [← mul_assoc, ← map_natCast C, ← map_mul, inv_mul_cancel₀ hk0, map_one, one_mul]
  rw [heq]
  exact close_const_mul _ hk

/-- Under the same hypothesis, `X_a^n` is congruent modulo `I` to a polynomial of degree `< n`. -/
theorem xpow_close (hp : ∀ b, 1 ≤ b → b ≤ n → Close I (psum (Fin n) ℂ b) (b - 1)) (a : Fin n) :
    Close I (X a ^ n) (n - 1) := by
  have hV := congrArg (Polynomial.eval (-X a : MvPolynomial (Fin n) ℂ))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ a) (by simp),
    Polynomial.eval_finsetSum, Fintype.card_fin, Finset.sum_range_succ'] at hV
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    esymm_zero, one_mul, Nat.sub_zero] at hV
  have hneg : (-X a : MvPolynomial (Fin n) ℂ) ^ n =
      -∑ j ∈ Finset.range n, esymm (Fin n) ℂ (j + 1) * (-X a) ^ (n - (j + 1)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hV.symm
  have hc : Close I ((-X a : MvPolynomial (Fin n) ℂ) ^ n) (n - 1) := by
    rw [hneg]
    refine (close_sum _ fun j hj => ?_).neg
    rw [Finset.mem_range] at hj
    have he := esymm_close hp (j + 1) (by omega) (by omega)
    have hx : Close I ((-X a : MvPolynomial (Fin n) ℂ) ^ (n - (j + 1))) (n - (j + 1)) :=
      close_of_totalDegree_le ((totalDegree_pow _ _).trans (by simp [totalDegree_neg]))
    exact (he.mul hx).mono (by omega)
  have hx : (X a : MvPolynomial (Fin n) ℂ) ^ n = (-1) ^ n * (-X a) ^ n := by
    rw [← mul_pow]; ring
  rw [hx]
  exact ((close_neg_one_pow n 0).mul hc).mono (by omega)

end Newton

/-! ## Monomials in a box -/

section Box

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (m : ℕ)

/-- The exponents `α` with `α s < m` for every variable `s`. -/
def boxSet : Finset (σ →₀ ℕ) :=
  (Finset.univ : Finset (σ → Fin m)).image
    fun g => Finsupp.equivFunOnFinite.symm fun s => (g s : ℕ)

variable {σ m} in
theorem mem_boxSet {α : σ →₀ ℕ} (h : ∀ s, α s < m) : α ∈ boxSet σ m :=
  Finset.mem_image.2 ⟨fun s => ⟨α s, h s⟩, Finset.mem_univ _, by ext s; simp⟩

/-- The span of the monomials with exponents in the box. -/
def boxSpan : Submodule ℂ (MvPolynomial σ ℂ) :=
  Submodule.span ℂ ((fun α => monomial α (1 : ℂ)) '' (boxSet σ m : Set (σ →₀ ℕ)))

variable {σ m}

/-- If every `X_s^m` is congruent modulo `J` to a polynomial of degree `< m`, every polynomial is
congruent modulo `J` to a combination of monomials in the box. -/
theorem mem_boxSpan_sup (J : Ideal (MvPolynomial σ ℂ)) (hm : ∀ _ : σ, 0 < m)
    (hrel : ∀ s, Close J (X s ^ m) (m - 1)) (f : MvPolynomial σ ℂ) :
    f ∈ boxSpan σ m ⊔ J.restrictScalars ℂ := by
  suffices H : ∀ D (f : MvPolynomial σ ℂ), f.totalDegree ≤ D →
      f ∈ boxSpan σ m ⊔ J.restrictScalars ℂ from H _ f le_rfl
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro f hf
  rw [f.as_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hαD : (α.sum fun _ e => e) ≤ D := (le_totalDegree hα).trans hf
  rw [show monomial α (f.coeff α) = f.coeff α • monomial α (1 : ℂ) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  refine Submodule.smul_mem _ _ ?_
  by_cases hbox : ∀ s, α s < m
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨α, mem_boxSet hbox, rfl⟩)
  · push Not at hbox
    obtain ⟨s, hs⟩ := hbox
    obtain ⟨r, hr, hmem⟩ := hrel s
    set β := α - Finsupp.single s m with hβ
    have hα' : α = β + Finsupp.single s m :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hs)).symm
    have hmon : monomial α (1 : ℂ) = monomial β 1 * X s ^ m := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, ← hα', one_mul]
    have hdec : monomial α (1 : ℂ) = monomial β 1 * (X s ^ m - r) + monomial β 1 * r := by
      rw [hmon]; ring
    rw [hdec]
    refine Submodule.add_mem _ (Submodule.mem_sup_right (J.mul_mem_left _ hmem)) ?_
    have hdegα : (α.sum fun _ e => e) = (β.sum fun _ e => e) + m := by
      rw [hα', Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl]
    have hm0 := hm s
    refine ih ((β.sum fun _ e => e) + (m - 1)) (by omega) _ ?_
    refine (totalDegree_mul _ _).trans (add_le_add ?_ hr)
    rw [totalDegree_monomial _ one_ne_zero]

end Box

/-! ## The two commuting `𝔤𝔩_n(ℂ)` actions -/

section Rep

open ComplexGenericLarge

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The matrix unit `E_pq` in the factor `i` of `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`. -/
abbrev unitPair (i : Fin 2) (p q : Fin n) : Fin 2 → Matrix (Fin n) (Fin n) ℂ :=
  Pi.single i (Matrix.single p q 1)

/-- The action of `E_pq` in the factor `i`. -/
def ee (i : Fin 2) (p q : Fin n) : Module.End ℂ V := prodAction π (unitPair i p q)

theorem prodAction_mul_sub (x y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) :
    prodAction π x * prodAction π y - prodAction π y * prodAction π x =
      prodAction π (x * y - y * x) := by
  rw [← Ring.lie_def, ← LieHom.map_lie, Ring.lie_def]

theorem unitPair_mul (i : Fin 2) (a b c d : Fin n) :
    unitPair i a b * unitPair i c d = if b = c then unitPair i a d else 0 := by
  rw [unitPair, unitPair, ← Pi.single_mul]
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, one_mul]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]

theorem isGlFamily_ee (i : Fin 2) : IsGlFamily (ee π i) := by
  intro a b c d
  simp only [ee]
  rw [prodAction_mul_sub, unitPair_mul, unitPair_mul]
  split_ifs <;> simp

theorem commute_ee (i j : Fin 2) (a b : Fin n) : Commute (ee π i a a) (ee π j b b) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  simp only [ee]
  rw [prodAction_mul_sub]
  have h : unitPair i a a * unitPair j b b - unitPair j b b * unitPair i a a = 0 := by
    funext t
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply]
    by_cases hi : t = i <;> by_cases hj : t = j
    · subst hi; subst hj
      by_cases hab : a = b
      · subst hab; simp
      · simp only [unitPair, Pi.single_eq_same]
        rw [Matrix.single_mul_single_of_ne _ _ _ _ hab,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab), sub_zero]
    · simp [Pi.single_eq_of_ne hj]
    · simp [Pi.single_eq_of_ne hi]
    · simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj]
  rw [h, map_zero]

/-- The diagonal generators of both factors. -/
def diagGen (s : Fin 2 × Fin n) : Module.End ℂ V := ee π s.1 s.2 s.2

/-- The commutative algebra generated by the diagonal of both factors. -/
def diagAlg : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range (diagGen π))

theorem diagAlg_commute {x y : Module.End ℂ V} (hx : x ∈ diagAlg π) (hy : y ∈ diagAlg π) :
    Commute x y := by
  have hgen : ∀ a ∈ Set.range (diagGen π), ∀ b ∈ Set.range (diagGen π), Commute a b := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact commute_ee π _ _ _ _
  have h1 : ∀ a ∈ Set.range (diagGen π), Commute a y := fun a ha =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => hgen a ha b hb
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun b hb => (h1 b hb).symm).symm

instance diagAlgCommRing : CommRing (diagAlg π) :=
  { (inferInstance : Ring (diagAlg π)) with
    mul_comm := fun x y => Subtype.ext (diagAlg_commute π x.2 y.2).eq }

/-- Polynomials in the diagonal generators `X_(i, a) ↦ E^{(i)}_aa`, acting on `V`. -/
def diagAct : MvPolynomial (Fin 2 × Fin n) ℂ →ₐ[ℂ] Module.End ℂ V :=
  (diagAlg π).val.comp
    (MvPolynomial.aeval fun s => ⟨diagGen π s, Algebra.subset_adjoin (Set.mem_range_self s)⟩)

theorem diagAct_X (s : Fin 2 × Fin n) : diagAct π (X s) = diagGen π s := by
  simp [diagAct]

theorem diagAct_mul_comm (f g : MvPolynomial (Fin 2 × Fin n) ℂ) :
    diagAct π (f * g) = diagAct π g * diagAct π f := by
  rw [mul_comm, map_mul]

end Rep

/-! ## `𝔫V` and the diagonal -/

section Jacquet

open ComplexGenericLarge

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- `prodAction π Y = π(½ (1 ⊗ Y₀ - i ⊗ iY₀ + 1 ⊗ Ȳ₁ + i ⊗ iȲ₁))`. -/
theorem prodAction_apply_eq (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) (v : V) :
    prodAction π Y v = (1 / 2 : ℂ) • (π ((1 : ℂ) ⊗ₜ[ℝ] Y 0) v -
      Complex.I • π ((1 : ℂ) ⊗ₜ[ℝ] (Complex.I • Y 0)) v +
      π ((1 : ℂ) ⊗ₜ[ℝ] conjMat (Y 1)) v +
      Complex.I • π ((1 : ℂ) ⊗ₜ[ℝ] (Complex.I • conjMat (Y 1))) v) := by
  rw [prodAction_apply, tensorEquiv_symm_apply, tensorInv]
  simp only [map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply]

/-- Strictly upper triangular matrices. -/
def StrictUpper (X : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0

/-- Diagonal matrices. -/
def IsDiag (X : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j : Fin n, i ≠ j → X i j = 0

theorem StrictUpper.smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : StrictUpper X) (c : ℂ) :
    StrictUpper (c • X) := fun i j hij => by simp [hX i j hij]

theorem StrictUpper.conj {X : Matrix (Fin n) (Fin n) ℂ} (hX : StrictUpper X) :
    StrictUpper (conjMat X) := fun i j hij => by simp [hX i j hij]

theorem IsDiag.smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsDiag X) (c : ℂ) :
    IsDiag (c • X) := fun i j hij => by simp [hX i j hij]

theorem IsDiag.conj {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsDiag X) :
    IsDiag (conjMat X) := fun i j hij => by simp [hX i j hij]

theorem prodAction_mem (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) (h0 : StrictUpper (Y 0))
    (h1 : StrictUpper (Y 1)) (v : V) : prodAction π Y v ∈ complexJacquetSubspace n π := by
  rw [prodAction_apply_eq]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)) ?_) (Submodule.smul_mem _ _ ?_))
  · exact mem_complexJacquetSubspace π h0 v
  · exact mem_complexJacquetSubspace π (h0.smul _) v
  · exact mem_complexJacquetSubspace π h1.conj v
  · exact mem_complexJacquetSubspace π (h1.conj.smul _) v

theorem pi_diag_mem {D : Matrix (Fin n) (Fin n) ℂ} (hD : IsDiag D) :
    ∀ w ∈ complexJacquetSubspace n π, π ((1 : ℂ) ⊗ₜ[ℝ] D) w ∈ complexJacquetSubspace n π := by
  intro w hw
  have hDsum : D = ∑ j, Matrix.single j j (D j j) := by
    ext p q
    rw [Matrix.sum_apply]
    by_cases h : p = q
    · subst h
      rw [Finset.sum_eq_single p (fun j _ hj => by simp [hj])
        (by simp)]
      simp
    · rw [hD p q h, Finset.sum_eq_zero]
      intro j _
      simp only [Matrix.single_apply]
      split_ifs with hj
      · exact absurd (hj.1.symm.trans hj.2) h
      · rfl
  rw [hDsum, TensorProduct.tmul_sum, map_sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun j _ => diag_mem_complexJacquetSubspace π j _ w hw

theorem prodAction_diag_mem (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) (h0 : IsDiag (Y 0))
    (h1 : IsDiag (Y 1)) :
    ∀ w ∈ complexJacquetSubspace n π, prodAction π Y w ∈ complexJacquetSubspace n π := by
  intro w hw
  rw [prodAction_apply_eq]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)) ?_) (Submodule.smul_mem _ _ ?_))
  · exact pi_diag_mem π h0 w hw
  · exact pi_diag_mem π (h0.smul _) w hw
  · exact pi_diag_mem π h1.conj w hw
  · exact pi_diag_mem π (h1.conj.smul _) w hw

theorem ee_up (i : Fin 2) :
    ∀ a b : Fin n, a < b → ∀ v, ee π i a b v ∈ complexJacquetSubspace n π := by
  intro a b hab v
  have h : ∀ t, StrictUpper (unitPair i a b t) := by
    intro t p q hqp
    by_cases ht : t = i
    · subst ht
      simp only [unitPair, Pi.single_eq_same, Matrix.single_apply]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd hab (not_lt.2 (Fin.le_iff_val_le_val.2 hqp))
      · rfl
    · simp [unitPair, Pi.single_eq_of_ne ht]
  exact prodAction_mem π _ (h 0) (h 1) v

theorem ee_diag (i : Fin 2) :
    ∀ a, ∀ v ∈ complexJacquetSubspace n π, ee π i a a v ∈ complexJacquetSubspace n π := by
  intro a
  have h : ∀ t, IsDiag (unitPair i a a t) := by
    intro t p q hpq
    by_cases ht : t = i
    · subst ht
      simp only [unitPair, Pi.single_eq_same, Matrix.single_apply]
      split_ifs with h
      · exact absurd (h.1.symm.trans h.2) hpq
      · rfl
    · simp [unitPair, Pi.single_eq_of_ne ht]
  exact prodAction_diag_mem π _ (h 0) (h 1)

/-! ## Gelfand's central elements act by scalars -/

theorem envelopingAction_pw (i : Fin 2) (k : ℕ) (p q : Fin n) :
    envelopingAction (prodAction π) (Kostant.pw ℂ (fun _ : Fin 2 => n) i k p q) =
      (Matrix.of (ee π i) ^ k) p q := by
  set f := envelopingAction (prodAction π)
  have hgen : f.mapMatrix (Kostant.genMat ℂ (fun _ : Fin 2 => n) i) = Matrix.of (ee π i) := by
    ext p q
    simp [f, Kostant.genMat, Kostant.gen, envelopingAction, Kostant.unit, ee, unitPair]
  calc f (Kostant.pw ℂ (fun _ : Fin 2 => n) i k p q)
      = f.mapMatrix (Kostant.genMat ℂ (fun _ : Fin 2 => n) i ^ k) p q := rfl
    _ = (Matrix.of (ee π i) ^ k) p q := by rw [map_pow, hgen]

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}

theorem trace_scalar (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (i : Fin 2) (k : ℕ) :
    ∃ c : ℂ, ∀ v, ∑ p, (Matrix.of (ee π i) ^ k) p p v = c • v := by
  obtain ⟨c, hc⟩ := prodAction_hasInfinitesimalCharacter hgk hirr hadm _
    (Kostant.gel_mem_center ℂ (fun _ : Fin 2 => n) i k)
  refine ⟨c, fun v => ?_⟩
  have h := LinearMap.congr_fun hc v
  rw [Kostant.gel, map_sum, LinearMap.sum_apply] at h
  simp only [envelopingAction_pw] at h
  rw [h, Module.algebraMap_end_apply]

/-- The polynomials whose image under `diagAct` maps `V` into `𝔫V`. -/
def annIdeal : Ideal (MvPolynomial (Fin 2 × Fin n) ℂ) where
  carrier := {f | ∀ v, diagAct π f v ∈ complexJacquetSubspace n π}
  add_mem' {f g} hf hg v := by
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (hf v) (hg v)
  zero_mem' v := by simp
  smul_mem' c f hf v := by
    rw [smul_eq_mul, diagAct_mul_comm, Module.End.mul_apply]
    exact hf _

theorem mem_annIdeal {f : MvPolynomial (Fin 2 × Fin n) ℂ} :
    f ∈ annIdeal π ↔ ∀ v, diagAct π f v ∈ complexJacquetSubspace n π :=
  Iff.rfl

theorem side_rel (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (i : Fin 2) (k : ℕ) :
    ∃ c : ℂ, rename (fun a : Fin n => (i, a)) (∑ a, gelPoly n k a - C c) ∈ annIdeal π := by
  obtain ⟨c, hc⟩ := trace_scalar π hgk hirr hadm i k
  refine ⟨c, fun v => ?_⟩
  set ψ := (diagAct π).comp (rename (R := ℂ) fun a : Fin n => (i, a)) with hψdef
  have hψ : ∀ a, ψ (X a) = ee π i a a := by
    intro a
    simp [hψdef, diagAct_X, diagGen]
  have hsum := Submodule.sum_mem (complexJacquetSubspace n π) (t := Finset.univ) fun a _ =>
    diag_pow (complexJacquetSubspace n π) (isGlFamily_ee π i) (ee_up π i) (ee_diag π i) ψ hψ
      k a v
  rw [Finset.sum_sub_distrib, hc] at hsum
  have heq : diagAct π (rename (fun a : Fin n => (i, a)) (∑ a, gelPoly n k a - C c)) v =
      -(c • v - ∑ a, ψ (gelPoly n k a) v) := by
    have : diagAct π (rename (fun a : Fin n => (i, a)) (∑ a, gelPoly n k a - C c)) =
        ψ (∑ a, gelPoly n k a - C c) := rfl
    rw [this, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, MvPolynomial.algHom_C,
      Module.algebraMap_end_apply, neg_sub]
  rw [heq]
  exact Submodule.neg_mem _ hsum

theorem psum_close (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (i : Fin 2) :
    ∀ b, 1 ≤ b → b ≤ n → Close ((annIdeal π).comap (rename (R := ℂ) fun a : Fin n => (i, a)))
      (psum (Fin n) ℂ b) (b - 1) := by
  intro b hb _
  obtain ⟨c, hc⟩ := side_rel π hgk hirr hadm i b
  refine ⟨psum (Fin n) ℂ b - (∑ a, gelPoly n b a - C c), ?_, ?_⟩
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have h : psum (Fin n) ℂ (b' + 1) - (∑ a, gelPoly n (b' + 1) a - C c) =
        -(∑ a, (gelPoly n (b' + 1) a - X a ^ (b' + 1))) + C c := by
      rw [MvPolynomial.psum, Finset.sum_sub_distrib]
      ring
    rw [h]
    refine (totalDegree_add _ _).trans (max_le ?_ ((totalDegree_C _).trans_le (Nat.zero_le _)))
    rw [totalDegree_neg]
    exact (totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun a _ => (totalDegree_gelPoly_sub b' a).trans (by omega))
  · rw [Ideal.mem_comap, sub_sub_cancel]
    exact hc

theorem xpow_rel (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (s : Fin 2 × Fin n) :
    Close (annIdeal π) (X s ^ n) (n - 1) := by
  obtain ⟨i, a⟩ := s
  have h := (xpow_close (psum_close π hgk hirr hadm i) a).rename (fun a : Fin n => (i, a))
  rwa [map_pow, rename_X] at h

/-- The image of `W` under the box monomials in the diagonal generators. -/
def boxImage (W : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ α : boxSet (Fin 2 × Fin n) n, W.map (diagAct π (monomial (α : Fin 2 × Fin n →₀ ℕ) 1))

theorem diagAct_mem_boxImage_sup (hgk : IsComplexGKModule n ρ π)
    (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ) (W : Submodule ℂ V)
    (f : MvPolynomial (Fin 2 × Fin n) ℂ) {w : V} (hw : w ∈ W) :
    diagAct π f w ∈ boxImage π W ⊔ complexJacquetSubspace n π := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1
    (mem_boxSpan_sup (annIdeal π) (fun s => s.2.pos) (xpow_rel π hgk hirr hadm) f)
  rw [map_add, LinearMap.add_apply]
  refine Submodule.add_mem_sup ?_ ((mem_annIdeal π).1 hz w)
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    exact Submodule.mem_iSup_of_mem (⟨α, hα⟩ : boxSet (Fin 2 × Fin n) n)
      (Submodule.mem_map_of_mem hw)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ c hx

theorem finiteDimensional_boxImage (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (boxImage π W) := by
  unfold boxImage
  infer_instance

end Jacquet

/-! ## Spanning: `V = ℂ[𝔥] W + 𝔫V` -/

section Spanning

open ComplexGenericLarge

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- Upper triangular matrices. -/
def Upper (X : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j : Fin n, j < i → X i j = 0

/-- Every matrix is a skew-Hermitian matrix plus an upper triangular one. -/
theorem exists_skew_add_upper (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Y X : Matrix (Fin n) (Fin n) ℂ, star Y = -Y ∧ Upper X ∧ Z = Y + X := by
  let L : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if j < i then Z i j else 0
  refine ⟨L - star L, Z - (L - star L), by rw [star_sub, star_star, neg_sub], ?_, by abel⟩
  intro i j hji
  simp [L, Matrix.star_apply, hji, hji.not_gt]

theorem sum_single_apply (d : Fin n → ℂ) (p q : Fin n) :
    (∑ j, Matrix.single j j (d j)) p q = if p = q then d p else 0 := by
  rw [Matrix.sum_apply]
  by_cases h : p = q
  · subst h
    rw [Finset.sum_eq_single p (fun j _ hj => by simp [hj]) (by simp)]
    simp
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [Matrix.single_apply]
    split_ifs with hj
    · exact absurd (hj.1.symm.trans hj.2) h
    · rfl

/-- The diagonal directions act through `diagAct`. -/
theorem pi_single_diag_eq (j : Fin n) (c : ℂ) :
    π ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single j j c) =
      diagAct π (C c * X (0, j) + C (starRingEnd ℂ c) * X (1, j)) := by
  rw [← tensorEquiv_symm_pairHom, ← prodAction_apply]
  have h : pairHom (Matrix.single j j c) =
      c • unitPair 0 j j + (starRingEnd ℂ c) • unitPair 1 j j := by
    funext t
    fin_cases t
    · ext p q
      simp [pairHom_zero, unitPair, Matrix.single_apply]
    · ext p q
      simp [pairHom_one, unitPair, Matrix.single_apply, apply_ite (starRingEnd ℂ)]
  rw [h, map_add, map_smul, map_smul, map_add, map_mul, map_mul, MvPolynomial.algHom_C,
    MvPolynomial.algHom_C, diagAct_X, diagAct_X]
  simp [diagGen, ee, Algebra.smul_def]

/-- The span of the vectors `diagAct f w`, `w ∈ W`. -/
def diagSpan (W : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ f, ∃ w ∈ W, u = diagAct π f w}

theorem diagAct_mem_diagSpan (W : Submodule ℂ V) (g : MvPolynomial (Fin 2 × Fin n) ℂ) {u : V}
    (hu : u ∈ diagSpan π W) : diagAct π g u ∈ diagSpan π W := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, w, hw, rfl⟩ := hx
    exact Submodule.subset_span ⟨g * f, w, hw, by rw [map_mul, Module.End.mul_apply]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem upper_stable (W : Submodule ℂ V) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Upper X) :
    ∀ u ∈ diagSpan π W ⊔ complexJacquetSubspace n π,
      π ((1 : ℂ) ⊗ₜ[ℝ] X) u ∈ diagSpan π W ⊔ complexJacquetSubspace n π := by
  intro u hu
  set D : Matrix (Fin n) (Fin n) ℂ := ∑ j, Matrix.single j j (X j j) with hDdef
  have hU : StrictUpper (X - D) := by
    intro i j hji
    rw [Matrix.sub_apply, hDdef, sum_single_apply]
    rcases (Fin.le_iff_val_le_val.2 hji).lt_or_eq with h | h
    · rw [hX i j h]
      simp [ne_of_gt h]
    · rw [h]
      simp
  have hsplit : π ((1 : ℂ) ⊗ₜ[ℝ] X) u = π ((1 : ℂ) ⊗ₜ[ℝ] (X - D)) u +
      ∑ j, π ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single j j (X j j)) u := by
    rw [← LinearMap.sum_apply, ← map_sum, ← TensorProduct.tmul_sum, ← hDdef,
      ← LinearMap.add_apply, ← map_add, ← TensorProduct.tmul_add, sub_add_cancel]
  rw [hsplit]
  refine Submodule.add_mem _ (Submodule.mem_sup_right (mem_complexJacquetSubspace π hU u))
    (Submodule.sum_mem _ fun j _ => ?_)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add]
  refine Submodule.add_mem_sup ?_ (diag_mem_complexJacquetSubspace π j _ z hz)
  rw [pi_single_diag_eq]
  exact diagAct_mem_diagSpan π W _ hy

/-- The smallest subspace containing `W` and stable under the upper triangular directions. -/
def upperClosure (W : Submodule ℂ V) : Submodule ℂ V :=
  sInf {S | W ≤ S ∧ ∀ X, Upper X → ∀ s ∈ S, π ((1 : ℂ) ⊗ₜ[ℝ] X) s ∈ S}

theorem le_upperClosure (W : Submodule ℂ V) : W ≤ upperClosure π W :=
  le_sInf fun _ hS => hS.1

theorem upperClosure_le (W S : Submodule ℂ V) (hW : W ≤ S)
    (hS : ∀ X, Upper X → ∀ s ∈ S, π ((1 : ℂ) ⊗ₜ[ℝ] X) s ∈ S) : upperClosure π W ≤ S :=
  sInf_le ⟨hW, hS⟩

theorem upperClosure_stable (W : Submodule ℂ V) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Upper X)
    {s : V} (hs : s ∈ upperClosure π W) : π ((1 : ℂ) ⊗ₜ[ℝ] X) s ∈ upperClosure π W :=
  Submodule.mem_sInf.2 fun S hS => hS.2 X hX s (Submodule.mem_sInf.1 hs S hS)

/-- If `W` is stable under `𝔨`, its upper triangular closure is stable under `𝔨`. -/
theorem upperClosure_skew (W : Submodule ℂ V)
    (hW : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → ∀ w ∈ W, π ((1 : ℂ) ⊗ₜ[ℝ] Y) w ∈ W) :
    ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y →
      ∀ s ∈ upperClosure π W, π ((1 : ℂ) ⊗ₜ[ℝ] Y) s ∈ upperClosure π W := by
  set B := upperClosure π W with hBdef
  let B' : Submodule ℂ V := B ⊓ ⨅ Y : {Y : Matrix (Fin n) (Fin n) ℂ // star Y = -Y},
    B.comap (π ((1 : ℂ) ⊗ₜ[ℝ] (Y : Matrix (Fin n) (Fin n) ℂ)))
  have hmem : ∀ s, s ∈ B' ↔ s ∈ B ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → π ((1 : ℂ) ⊗ₜ[ℝ] Y) s ∈ B := by
    intro s
    simp only [B', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, Subtype.forall]
  have hle : B ≤ B' := by
    refine upperClosure_le π W B' (fun w hw => (hmem w).2
      ⟨le_upperClosure π W hw, fun Y hY => le_upperClosure π W (hW Y hY w hw)⟩) ?_
    intro X hX s hs
    rw [hmem] at hs ⊢
    refine ⟨upperClosure_stable π W hX hs.1, fun Y hY => ?_⟩
    obtain ⟨Y', X', hY', hX', hZ⟩ := exists_skew_add_upper (Y * X - X * Y)
    have hc := LinearMap.congr_fun (complex_map_commutator π Y X) s
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
    have h : π ((1 : ℂ) ⊗ₜ[ℝ] Y) (π ((1 : ℂ) ⊗ₜ[ℝ] X) s) =
        π ((1 : ℂ) ⊗ₜ[ℝ] X) (π ((1 : ℂ) ⊗ₜ[ℝ] Y) s) +
          (π ((1 : ℂ) ⊗ₜ[ℝ] Y') s + π ((1 : ℂ) ⊗ₜ[ℝ] X') s) := by
      rw [← LinearMap.add_apply, ← map_add, ← TensorProduct.tmul_add, ← hZ, hc]
      abel
    rw [h]
    exact B.add_mem (upperClosure_stable π W hX (hs.2 Y hY))
      (B.add_mem (hs.2 Y' hY') (upperClosure_stable π W hX' hs.1))
  intro Y hY s hs
  exact ((hmem s).1 (hle hs)).2 Y hY

theorem upperClosure_pi_stable (W : Submodule ℂ V)
    (hW : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → ∀ w ∈ W, π ((1 : ℂ) ⊗ₜ[ℝ] Y) w ∈ W) :
    ∀ x, ∀ s ∈ upperClosure π W, π x s ∈ upperClosure π W := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c Z =>
    intro s hs
    obtain ⟨Y, X, hY, hX, rfl⟩ := exists_skew_add_upper Z
    have h : c ⊗ₜ[ℝ] (Y + X) = c • ((1 : ℂ) ⊗ₜ[ℝ] Y + (1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [← TensorProduct.tmul_add, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply]
    exact Submodule.smul_mem _ c (Submodule.add_mem _ (upperClosure_skew π W hW Y hY s hs)
      (upperClosure_stable π W hX hs))
  | add x y hx hy =>
    intro s hs
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (hx s hs) (hy s hs)

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}

theorem upperClosure_eq_top (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (W : Submodule ℂ V) (hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W)
    (hW : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → ∀ w ∈ W, π ((1 : ℂ) ⊗ₜ[ℝ] Y) w ∈ W)
    (hW0 : W ≠ ⊥) : upperClosure π W = ⊤ := by
  set G : Submodule ℂ V := sInf {S | W ≤ S ∧ ∀ x, ∀ s ∈ S, π x s ∈ S} with hGdef
  have hGπ : ∀ x, ∀ s ∈ G, π x s ∈ G := fun x s hs =>
    Submodule.mem_sInf.2 fun S hS => hS.2 x s (Submodule.mem_sInf.1 hs S hS)
  have hWG : W ≤ G := le_sInf fun _ hS => hS.1
  have hGρ : ∀ k, ∀ s ∈ G, ρ k s ∈ G := by
    intro k
    have hle : G ≤ G.comap (ρ k) := by
      refine sInf_le ⟨fun w hw => hWG (hWK k w hw), fun x s hs => ?_⟩
      rw [Submodule.mem_comap] at hs ⊢
      have h := LinearMap.congr_fun (rho_mul_pi hgk.2.2.2 k x) s
      simp only [Module.End.mul_apply] at h
      rw [h]
      exact hGπ _ _ hs
    exact fun s hs => hle hs
  have hG : G = ⊤ := (hirr.2 G hGρ hGπ).resolve_left fun h => hW0 (le_bot_iff.1 (h ▸ hWG))
  rw [eq_top_iff, ← hG]
  exact sInf_le ⟨le_upperClosure π W, upperClosure_pi_stable π W hW⟩

theorem diagSpan_sup_eq_top (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (W : Submodule ℂ V) (hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W)
    (hW : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → ∀ w ∈ W, π ((1 : ℂ) ⊗ₜ[ℝ] Y) w ∈ W)
    (hW0 : W ≠ ⊥) : diagSpan π W ⊔ complexJacquetSubspace n π = ⊤ := by
  rw [eq_top_iff, ← upperClosure_eq_top π hgk hirr W hWK hW hW0]
  refine upperClosure_le π W _ (fun w hw => Submodule.mem_sup_left
    (Submodule.subset_span ⟨1, w, hw, by simp⟩)) fun X hX => upper_stable π W X hX

end Spanning

/-! ## `U(n)`-stable subspaces are stable under `𝔲(n)` -/

section Derivative

variable {n : ℕ}

/-- The one-parameter subgroup `t ↦ exp(tY)` of `U(n)`, `Y` skew-Hermitian. -/
def expCurve (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y) (t : ℝ) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp (t • Y),
    ComplexDuality.LieInvariance.exp_smul_mem_unitaryGroup
      (by rwa [← Matrix.star_eq_conjTranspose]) t⟩

theorem expCurve_zero (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y) :
    expCurve Y hY 0 = 1 := by
  apply Subtype.ext
  simp [expCurve, NormedSpace.exp_zero]

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_expCurve (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y) (i j : Fin n) :
    HasDerivAt (fun t => (expCurve Y hY t : Matrix (Fin n) (Fin n) ℂ) i j) (Y i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- A `U(n)`-stable subspace is stable under `π(1 ⊗ Y)`, `Y` skew-Hermitian: if `ℓ` vanishes
on `W`, then `t ↦ ℓ(ρ(exp tY) w)` vanishes identically, so its derivative `ℓ(π(1 ⊗ Y) w)` at
`0` vanishes. -/
theorem skew_stable (hgk : IsComplexGKModule n ρ π) (W : Submodule ℂ V)
    (hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y) :
    ∀ w ∈ W, π ((1 : ℂ) ⊗ₜ[ℝ] Y) w ∈ W := by
  intro w hw
  by_contra hnot
  obtain ⟨ℓ, hℓ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hd := hgk.2.2.1 (expCurve Y hY) Y (expCurve_zero Y hY) (hasDerivAt_expCurve Y hY) w ℓ
  have hzero : (fun t => ℓ (ρ (expCurve Y hY t) w)) = fun _ => 0 := by
    funext t
    have hm : ℓ (ρ (expCurve Y hY t) w) ∈ W.map ℓ := Submodule.mem_map_of_mem (hWK _ w hw)
    rw [hmap] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  rw [hzero] at hd
  exact hℓ ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).unique hd).symm

end Derivative

/-! ## The theorem -/

open ComplexGenericLarge in
/-- **The Jacquet module of an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module is
finite-dimensional.** -/
theorem complexJacquetModule_finiteDimensional {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) :
    FiniteDimensional ℂ (V ⧸ complexJacquetSubspace n π) := by
  have := hirr.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set W := FiniteVectors.orbitSpan ρ v with hWdef
  have hWfin : Module.Finite ℂ W := hgk.1 v
  have hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W := fun k w hw =>
    (FiniteVectors.orbitSubrepresentation ρ v).apply_mem_toSubmodule k hw
  have hW0 : W ≠ ⊥ := fun h => hv ((Submodule.mem_bot ℂ).1
    (h ▸ FiniteVectors.self_mem_orbitSpan ρ v))
  have htop := diagSpan_sup_eq_top π hgk hirr W hWK (skew_stable hgk W hWK) hW0
  have hle : diagSpan π W ≤ boxImage π W ⊔ complexJacquetSubspace n π := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, w, hw, rfl⟩
    exact diagAct_mem_boxImage_sup π hgk hirr hadm W f hw
  have hall : ∀ u : V, u ∈ boxImage π W ⊔ complexJacquetSubspace n π := by
    intro u
    have hu : u ∈ diagSpan π W ⊔ complexJacquetSubspace n π := by rw [htop]; trivial
    exact (sup_le hle le_sup_right) hu
  have := finiteDimensional_boxImage π W
  refine Module.Finite.of_surjective
    ((complexJacquetSubspace n π).mkQ ∘ₗ (boxImage π W).subtype) ?_
  intro q
  obtain ⟨u, rfl⟩ := (complexJacquetSubspace n π).mkQ_surjective q
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hall u)
  refine ⟨⟨y, hy⟩, ?_⟩
  simp [(Submodule.Quotient.mk_eq_zero _).2 hz]

end ComplexJacquetFinite

universe uV

/-- **Finite dimensionality of the Jacquet module** (the first half of
`ComplexJacquetModuleFiniteStatement`; Wallach 1979, 4.14 with 4.15–4.16): for an irreducible
admissible `(𝔤𝔩_n(ℂ), U(n))`-module, `V/𝔫V` is finite-dimensional. -/
def ComplexJacquetModuleFiniteDimensionalStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      FiniteDimensional ℂ (V ⧸ complexJacquetSubspace n π)

/-- **Nonvanishing of the Jacquet module** (Casselman's theorem proper, the second half of
`ComplexJacquetModuleFiniteStatement`; Wallach 1979, 4.14): for an irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module, `𝔫V ≠ V`. -/
def ComplexJacquetModuleNonzeroStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      complexJacquetSubspace n π ≠ ⊤

/-- Proof of `ComplexJacquetModuleFiniteDimensionalStatement`. -/
theorem complexJacquetModuleFiniteDimensional :
    ComplexJacquetModuleFiniteDimensionalStatement.{uV} :=
  fun _ _ _ _ _ _ hgk hirr hadm =>
    ComplexJacquetFinite.complexJacquetModule_finiteDimensional hgk hirr hadm

/-- `ComplexJacquetModuleFiniteStatement` is the conjunction of the two halves; the first is
proved here. -/
theorem complexJacquetModuleFinite_of_nonzero :
    ComplexJacquetModuleNonzeroStatement.{uV} → ComplexJacquetModuleFiniteStatement.{uV} :=
  fun h n V _ _ ρ π hgk hirr hadm =>
    ⟨complexJacquetModuleFiniteDimensional n V ρ π hgk hirr hadm, h n V ρ π hgk hirr hadm⟩

end Langlands.Archimedean
