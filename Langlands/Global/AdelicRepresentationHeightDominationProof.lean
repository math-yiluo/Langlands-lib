import Langlands.Global.AdelicRepresentationHeightDominationStatement
import Langlands.Global.RepresentationHeightDominationProof

/-! # Closed embeddings dominate full adelic representation heights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.RepresentationGrowth

section PolynomialBounds

variable (F : Type u) [Field F] [NumberField F]
  {X σ : Type*} (z : X → σ → Adeles F)
  (hi : X → InfinitePlace F → ℝ) (hf : X → FinitePlace F → ℝ)
  (hi1 : ∀ x v, 1 ≤ hi x v) (hf1 : ∀ x v, 1 ≤ hf x v)
  (hzi : ∀ x c v, ‖infiniteProjection F v (z x c)‖ ≤ hi x v)
  (hzf : ∀ x c v, ‖finiteProjection F v (z x c)‖ ≤ hf x v)

include hi1 hf1 hzi hzf in
/-- A fixed adelic polynomial has a single degree at all places. Its finite-place
constants have finite multiplicative support. -/
theorem exists_adelic_polynomial_bound (p : MvPolynomial σ F) :
    ∃ (A : InfinitePlace F → ℝ) (B : FinitePlace F → ℝ) (e : ℕ),
      (∀ v, 1 ≤ A v) ∧ (∀ v, 1 ≤ B v) ∧ B.HasFiniteMulSupport ∧
      (∀ x v, ‖infiniteProjection F v (aeval (z x) p)‖ ≤ A v * hi x v ^ e) ∧
      (∀ x v, ‖finiteProjection F v (aeval (z x) p)‖ ≤ B v * hf x v ^ e) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      let a : Adeles F := algebraMap F (Adeles F) r
      refine ⟨(fun v => max ‖infiniteProjection F v a‖ 1),
        (fun v => max ‖finiteProjection F v a‖ 1), 0,
        (fun _ => le_max_right _ _), (fun _ => le_max_right _ _), ?_, ?_, ?_⟩
      · apply Filter.eventually_cofinite.mp
        filter_upwards [a.2.property] with v hv
        have hv' : ‖finiteProjection F v a‖ ≤ 1 := by
          have hv0 : a.2 v ∈ v.adicCompletionIntegers F := hv
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hv0
          exact Valued.toNormedField.norm_le_one_iff.mpr hv0
        exact max_eq_right hv'
      · intro x v
        simpa only [aeval_C, pow_zero, mul_one] using
          le_max_left ‖infiniteProjection F v a‖ 1
      · intro x v
        simpa only [aeval_C, pow_zero, mul_one] using
          le_max_left ‖finiteProjection F v a‖ 1
  | add p q hp hq =>
      obtain ⟨A, B, e, hA, hB, hBs, hpi, hpf⟩ := hp
      obtain ⟨D, E, d, hD, hE, hEs, hqi, hqf⟩ := hq
      refine ⟨(fun v => A v + D v), (fun v => max (B v) (E v)), max e d,
        (fun v => by linarith [hA v, hD v]),
        (fun v => (hB v).trans (le_max_left _ _)), hBs.max hEs, ?_, ?_⟩
      · intro x v
        rw [map_add, map_add]
        calc
          _ ≤ ‖infiniteProjection F v (aeval (z x) p)‖ +
              ‖infiniteProjection F v (aeval (z x) q)‖ := norm_add_le _ _
          _ ≤ A v * hi x v ^ e + D v * hi x v ^ d := add_le_add (hpi x v) (hqi x v)
          _ ≤ A v * hi x v ^ max e d + D v * hi x v ^ max e d :=
            add_le_add
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hi1 x v) (le_max_left e d))
                (zero_le_one.trans (hA v)))
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hi1 x v) (le_max_right e d))
                (zero_le_one.trans (hD v)))
          _ = _ := (add_mul _ _ _).symm
      · intro x v
        rw [map_add, map_add]
        apply (IsUltrametricDist.norm_add_le_max _ _).trans
        apply max_le
        · exact (hpf x v).trans (mul_le_mul (le_max_left _ _)
            (pow_le_pow_right₀ (hf1 x v) (le_max_left e d))
            (pow_nonneg (zero_le_one.trans (hf1 x v)) _)
            (zero_le_one.trans ((hB v).trans (le_max_left _ _))))
        · exact (hqf x v).trans (mul_le_mul (le_max_right _ _)
            (pow_le_pow_right₀ (hf1 x v) (le_max_right e d))
            (pow_nonneg (zero_le_one.trans (hf1 x v)) _)
            (zero_le_one.trans ((hB v).trans (le_max_left _ _))))
  | mul_X p c hp =>
      obtain ⟨A, B, e, hA, hB, hBs, hpi, hpf⟩ := hp
      refine ⟨A, B, e + 1, hA, hB, hBs, ?_, ?_⟩
      · intro x v
        rw [map_mul, aeval_X, map_mul, norm_mul]
        calc
          _ ≤ (A v * hi x v ^ e) * hi x v :=
            mul_le_mul (hpi x v) (hzi x c v) (norm_nonneg _)
              (mul_nonneg (zero_le_one.trans (hA v))
                (pow_nonneg (zero_le_one.trans (hi1 x v)) _))
          _ = _ := by rw [pow_succ]; ring
      · intro x v
        rw [map_mul, aeval_X, map_mul, norm_mul]
        calc
          _ ≤ (B v * hf x v ^ e) * hf x v :=
            mul_le_mul (hpf x v) (hzf x c v) (norm_nonneg _)
              (mul_nonneg (zero_le_one.trans (hB v))
                (pow_nonneg (zero_le_one.trans (hf1 x v)) _))
          _ = _ := by rw [pow_succ]; ring

include hi1 hf1 hzi hzf in
/-- A finite family of polynomials admits common constants and a common degree. -/
theorem exists_adelic_polynomial_family_bound {κ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ F) :
    ∃ (A : InfinitePlace F → ℝ) (B : FinitePlace F → ℝ) (e : ℕ),
      (∀ v, 1 ≤ A v) ∧ (∀ v, 1 ≤ B v) ∧ B.HasFiniteMulSupport ∧
      (∀ c x v, ‖infiniteProjection F v (aeval (z x) (p c))‖ ≤ A v * hi x v ^ e) ∧
      (∀ c x v, ‖finiteProjection F v (aeval (z x) (p c))‖ ≤ B v * hf x v ^ e) := by
  choose A B e hA hB hBs hpi hpf using
    fun c => exists_adelic_polynomial_bound F z hi hf hi1 hf1 hzi hzf (p c)
  have hprod : ∀ (f : κ → ℝ), (∀ c, 1 ≤ f c) → ∀ c, f c ≤ ∏ d, f d := by
    intro f hf c
    calc
      f c = ∏ d ∈ ({c} : Finset κ), f d := by simp
      _ ≤ ∏ d, f d := Finset.prod_le_prod_of_subset_of_one_le₀
        (Finset.subset_univ _) (fun d _ => zero_le_one.trans (hf d)) (fun d _ _ => hf d)
  refine ⟨(fun v => ∏ c, A c v), (fun v => ∏ c, B c v), ∑ c, e c,
    (fun v => Finset.one_le_prod₀ fun c _ => hA c v),
    (fun v => Finset.one_le_prod₀ fun c _ => hB c v),
    Function.HasFiniteMulSupport.prod hBs Finset.univ, ?_, ?_⟩
  · intro c x v
    exact (hpi c x v).trans (mul_le_mul (hprod _ (fun c => hA c v) c)
      (pow_le_pow_right₀ (hi1 x v) (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)))
      (pow_nonneg (zero_le_one.trans (hi1 x v)) _)
      (zero_le_one.trans (Finset.one_le_prod₀ fun c _ => hA c v)))
  · intro c x v
    exact (hpf c x v).trans (mul_le_mul (hprod _ (fun c => hB c v) c)
      (pow_le_pow_right₀ (hf1 x v) (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)))
      (pow_nonneg (zero_le_one.trans (hf1 x v)) _)
      (zero_le_one.trans (Finset.one_le_prod₀ fun c _ => hB c v)))

end PolynomialBounds

section LocalCoordinates

open GroupScheme.GeneralLinear

variable {R K : Type*} [CommRing R] [NormedField K] {n : ℕ}
  (f : R →+* K) (a : Matrix.GeneralLinearGroup (Fin n) R)

private theorem norm_coordinate_le_localMaximum (c : Coordinate (Fin n)) :
    ‖f (values a c)‖ ≤ MatrixInverseHeight.localMaximum f a := by
  cases c with
  | entry i j => exact MatrixInverseHeight.entry_le_localMaximum f a i j
  | inverseEntry i j =>
      simpa only [values, MatrixInverseHeight.localMaximum_inv] using
        MatrixInverseHeight.entry_le_localMaximum f a⁻¹ i j

private theorem localMaximum_le_of_coordinates {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ c : Coordinate (Fin n), ‖f (values a c)‖ ≤ C) :
    MatrixInverseHeight.localMaximum f a ≤ C := by
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro j
    exact hc (Coordinate.entry i j)
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro j
    exact hc (Coordinate.inverseEntry i j)

end LocalCoordinates

open GroupScheme.GeneralLinear MatrixInverseHeight AdelicMatrixHeight in
/-- A scheme-theoretic closed matrix embedding dominates every matrix representation
for the fixed full adelic height, with one constant and exponent before the point. -/
theorem closedImmersionAdelicHeightDomination :
    ClosedImmersionAdelicHeightDominationStatement.{u} := by
  intro F _ _ G N M rho sigma hN hM hrho
  choose p hp using exists_coordinate_polynomial rho sigma hrho
  let : Fintype (Coordinate (Fin M)) := Fintype.ofEquiv
    ((Fin M × Fin M) ⊕ (Fin M × Fin M))
    { toFun := fun x => match x with
        | Sum.inl (i, j) => Coordinate.entry i j
        | Sum.inr (i, j) => Coordinate.inverseEntry i j
      invFun := fun c => match c with
        | Coordinate.entry i j => Sum.inl (i, j)
        | Coordinate.inverseEntry i j => Sum.inr (i, j)
      left_inv := by intro x; rcases x with ⟨i, j⟩ | ⟨i, j⟩ <;> rfl
      right_inv := by intro c; cases c <;> rfl }
  let hi (g : AdelicGroupPoints F G) (v : InfinitePlace F) : ℝ :=
    N * infiniteLocal F N (adelicMatrix F G rho g) v
  let hf (g : AdelicGroupPoints F G) (v : FinitePlace F) : ℝ :=
    finiteLocal F N (adelicMatrix F G rho g) v
  have hi1 : ∀ g v, 1 ≤ hi g v := fun g v =>
    one_le_nat_mul_localMaximum (infiniteProjection F v) hN _
  have hf1 : ∀ g v, 1 ≤ hf g v := fun g v => one_le_finiteLocal F N hN _ v
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  have hzi : ∀ g c v,
      ‖infiniteProjection F v (values (adelicMatrix F G rho g) c)‖ ≤ hi g v := by
    intro g c v
    exact (norm_coordinate_le_localMaximum _ _ c).trans
      (le_mul_of_one_le_left (localMaximum_nonneg _ _) hN1)
  have hzf : ∀ g c v,
      ‖finiteProjection F v (values (adelicMatrix F G rho g) c)‖ ≤ hf g v := by
    intro g c v
    exact norm_coordinate_le_localMaximum _ _ c
  obtain ⟨A, B, e, hA, hB, hBs, hpi, hpf⟩ := exists_adelic_polynomial_family_bound F
    (fun g => values (adelicMatrix F G rho g)) hi hf hi1 hf1 hzi hzf p
  have hpoly : ∀ c g, values (adelicMatrix F G sigma g) c =
      aeval (values (adelicMatrix F G rho g)) (p c) := fun c g =>
    hp c (CommAlgCat.of F (Adeles F)) g
  have hli : ∀ g v, infiniteLocal F M (adelicMatrix F G sigma g) v ≤ A v * hi g v ^ e := by
    intro g v
    apply localMaximum_le_of_coordinates
    · exact mul_nonneg (zero_le_one.trans (hA v))
        (pow_nonneg (zero_le_one.trans (hi1 g v)) _)
    · intro c
      rw [hpoly]
      exact hpi c g v
  have hlf : ∀ g v, finiteLocal F M (adelicMatrix F G sigma g) v ≤ B v * hf g v ^ e := by
    intro g v
    apply localMaximum_le_of_coordinates
    · exact mul_nonneg (zero_le_one.trans (hB v))
        (pow_nonneg (zero_le_one.trans (hf1 g v)) _)
    · intro c
      rw [hpoly]
      exact hpf c g v
  let Ci : ℝ := ∏ v : InfinitePlace F, ((M : ℝ) * A v) ^ v.mult
  let Cf : ℝ := ∏ᶠ v : FinitePlace F, B v
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.succ_le_of_lt hM
  have hCi : 1 ≤ Ci := Finset.one_le_prod₀ fun v _ =>
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hM1 (hA v))
  have hCf : 1 ≤ Cf := one_le_finprod hB
  refine ⟨Ci * Cf, one_le_mul_of_one_le_of_one_le hCi hCf, e, fun g => ?_⟩
  have hfin : (∏ᶠ v : FinitePlace F, finiteLocal F M (adelicMatrix F G sigma g) v) ≤
      Cf * (∏ᶠ v : FinitePlace F, hf g v) ^ e := by
    have hfs := hasFiniteMulSupport_finiteLocal F N hN (adelicMatrix F G rho g)
    have hfs' : (fun v => hf g v ^ e).HasFiniteMulSupport := by
      exact hfs.fun_comp (one_pow e)
    dsimp only [Cf]
    rw [finprod_pow hfs, ← finprod_mul_distrib hBs hfs']
    apply finprod_le_finprod₀
      (hasFiniteMulSupport_finiteLocal F M hM (adelicMatrix F G sigma g))
      (fun v => localMaximum_nonneg _ _) (hBs.mul hfs')
    exact hlf g
  have hinf : (∏ v : InfinitePlace F,
      ((M : ℝ) * infiniteLocal F M (adelicMatrix F G sigma g) v) ^ v.mult) ≤
      Ci * (∏ v : InfinitePlace F, hi g v ^ v.mult) ^ e := by
    calc
      _ ≤ ∏ v : InfinitePlace F, (((M : ℝ) * A v) * hi g v ^ e) ^ v.mult := by
        apply Finset.prod_le_prod₀
        · intro v _
          exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _
        · intro v _
          apply pow_le_pow_left₀
            (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _))
          calc
            _ ≤ (M : ℝ) * (A v * hi g v ^ e) :=
              mul_le_mul_of_nonneg_left (hli g v) (Nat.cast_nonneg _)
            _ = _ := by ring
      _ = _ := by
        simp only [Ci, mul_pow, Finset.prod_mul_distrib]
        congr 1
        calc
          _ = ∏ v : InfinitePlace F, (hi g v ^ v.mult) ^ e :=
            Finset.prod_congr rfl fun v _ => pow_right_comm _ _ _
          _ = _ := Finset.prod_pow _ _ _
  change _ ≤ (Ci * Cf) *
    ((∏ v : InfinitePlace F, hi g v ^ v.mult) * ∏ᶠ v : FinitePlace F, hf g v) ^ e
  calc
    _ ≤ (Ci * (∏ v : InfinitePlace F, hi g v ^ v.mult) ^ e) *
        (Cf * (∏ᶠ v : FinitePlace F, hf g v) ^ e) :=
      mul_le_mul hinf hfin (finprod_nonneg fun v => localMaximum_nonneg _ _)
        (mul_nonneg (zero_le_one.trans hCi)
          (pow_nonneg (Finset.prod_nonneg fun v _ =>
            pow_nonneg (zero_le_one.trans (hi1 g v)) _) _))
    _ = _ := by rw [mul_pow]; ring

end Langlands.Global.RepresentationGrowth
