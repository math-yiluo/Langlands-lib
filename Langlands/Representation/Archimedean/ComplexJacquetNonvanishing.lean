import Langlands.Representation.Archimedean.ComplexJacquetKernel

/-!
# The Jacquet integral does not vanish on strictly dominant complex principal series

For strictly dominant phase-power characters `χ` of `GL_n(ℂ)` whose restrictions to the unit
circle are integral powers `χ_l(u) = u^{p_l}`, the Jacquet integral `Λ_n`
(`ComplexJacquetDual.jacquet`) is a nonzero functional on the `U(n)`-finite principal series
(`ComplexJacquetNonvanishing.exists_jacquet_ne_zero`).
-/

noncomputable section

open MeasureTheory Matrix Filter Topology ComplexConjugate

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexJacquetNonvanishing

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexPartialJacquet
  ComplexJacquetLimit ComplexJacquetDual ComplexJacquetKernel ComplexGramFormula
  Langlands.GeneralLinear ComplexDuality ComplexPrincipalSeriesExtension

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-! ## Continuity of the Jacquet integral -/

/-- **Continuity.** The Jacquet integral is continuous for convergence on `U(n)` that is
bounded uniformly on `U(n)`. -/
theorem tendsto_jacquet : ∀ (n : ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}, IsPhasePower χ e →
    IsStrictlyDominant e (n - 1) →
    ∀ {f : ℕ → Langlands.GeneralLinear n ℂ → ℂ} {f₀ : Langlands.GeneralLinear n ℂ → ℂ},
    (∀ N, f N ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) →
    f₀ ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
    ∀ {C : ℝ}, (∀ N, ∀ k ∈ unitaryCompact ℂ n, ‖f N k‖ ≤ C) →
    (∀ k ∈ unitaryCompact ℂ n, Tendsto (fun N => f N k) atTop (𝓝 (f₀ k))) →
    Tendsto (fun N => jacquet n (f N)) atTop (𝓝 (jacquet n f₀))
  | 0, _, _, _, _, _, _, _, _, _, _, hlim => hlim 1 (unitaryCompact ℂ 0).one_mem
  | m + 1, χ, e, hχ, he, f, f₀, hf, hf₀, C, hC, hlim => by
      have he' : IsStrictlyDominant e m := by simpa using he
      set D : (Fin m → ℂ) → ℝ := fun x => C * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ chartExponent e l
        with hD
      have hDi : Integrable D :=
        (integrable_prod_one_add_sq_rpow (chartExponent_lt he')).const_mul C
      refine tendsto_jacquet m hχ.shift (isStrictlyDominant_shift he')
        (fun N => jacquetStep_mem hχ he' (hf N)) (jacquetStep_mem hχ he' hf₀) (C := ∫ x, D x)
        (fun N k hk => ?_) (fun k hk => ?_)
      · exact norm_integral_le_of_norm_le hDi (ae_of_all _ fun x =>
          norm_le_of_mem_principalSeries hχ he' (hf N).1 (hC N) x (iotaGL_mem_unitaryCompact hk))
      · refine tendsto_integral_of_dominated_convergence D (fun N =>
          ((hf N).1.1.continuous.comp
            (continuous_chartGL.mul continuous_const)).aestronglyMeasurable)
          hDi (fun N => ae_of_all _ fun x => norm_le_of_mem_principalSeries hχ he' (hf N).1 (hC N)
            x (iotaGL_mem_unitaryCompact hk)) (ae_of_all _ fun x => ?_)
        obtain ⟨a, u, κ, hκ, hy⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary
          (chartGL x * iotaGL k)
        have h1 : (fun N => f N (chartGL x * iotaGL k)) =
            fun N => principalSeriesCharacter ℂ (m + 1) χ a * f N κ :=
          funext fun N => by rw [hy, (hf N).1.2 a u κ]
        rw [h1, hy, hf₀.1.2 a u κ]
        exact (hlim κ hκ).const_mul _

/-! ## Translate-finite functions on `U(n)` -/

section TranslateFinite

variable {n : ℕ}

/-- The right translates `x ↦ f(x k)`, `k ∈ U(n)`, of `f` span a finite-dimensional space. -/
def IsTranslateFinite (f : Matrix.unitaryGroup (Fin n) ℂ → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
    fun x => f (x * k)))

theorem isTranslateFinite_const (c : ℂ) : IsTranslateFinite (n := n) (fun _ => c) := by
  unfold IsTranslateFinite
  have h : Set.range (fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x : Matrix.unitaryGroup (Fin n) ℂ => (fun _ => c) (x * k)) ⊆ {fun _ => c} := by
    rintro _ ⟨k, rfl⟩
    rfl
  have : FiniteDimensional ℂ (Submodule.span ℂ
      ({fun _ => c} : Set (Matrix.unitaryGroup (Fin n) ℂ → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono h)

theorem isTranslateFinite_add {f g : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hf : IsTranslateFinite f) (hg : IsTranslateFinite g) :
    IsTranslateFinite (fun x => f x + g x) := by
  unfold IsTranslateFinite at *
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x => (fun x => f x + g x) (x * k)) ≤
      Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => f (x * k)) ⊔
        Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
          fun x => g (x * k)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have : (fun x : Matrix.unitaryGroup (Fin n) ℂ => (fun x => f x + g x) (x * k)) =
        (fun x => f (x * k)) + fun x => g (x * k) := rfl
    change (fun x : Matrix.unitaryGroup (Fin n) ℂ => (fun x => f x + g x) (x * k)) ∈ _
    rw [this]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem isTranslateFinite_mul {f g : Matrix.unitaryGroup (Fin n) ℂ → ℂ}
    (hf : IsTranslateFinite f) (hg : IsTranslateFinite g) :
    IsTranslateFinite (fun x => f x * g x) := by
  unfold IsTranslateFinite at *
  set A := Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
    fun x => f (x * k))
  set B := Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
    fun x => g (x * k))
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x => (fun x => f x * g x) (x * k)) ≤ A * B := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have : (fun x : Matrix.unitaryGroup (Fin n) ℂ => (fun x => f x * g x) (x * k)) =
        (fun x => f (x * k)) * fun x => g (x * k) := rfl
    change (fun x : Matrix.unitaryGroup (Fin n) ℂ => (fun x => f x * g x) (x * k)) ∈ _
    rw [this]
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  have hAB : (A * B).FG := (Submodule.fg_iff_finiteDimensional A).mpr hf |>.mul
    ((Submodule.fg_iff_finiteDimensional B).mpr hg)
  have : FiniteDimensional ℂ (A * B) := (Submodule.fg_iff_finiteDimensional _).mp hAB
  exact Submodule.finiteDimensional_of_le hle

theorem isTranslateFinite_pow {f : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hf : IsTranslateFinite f)
    (N : ℕ) : IsTranslateFinite (fun x => f x ^ N) := by
  induction N with
  | zero => simpa using isTranslateFinite_const (n := n) 1
  | succ N ih => simpa [pow_succ] using isTranslateFinite_mul ih hf

theorem isTranslateFinite_prod {ι : Type*} (s : Finset ι)
    (f : ι → Matrix.unitaryGroup (Fin n) ℂ → ℂ) (hf : ∀ i ∈ s, IsTranslateFinite (f i)) :
    IsTranslateFinite (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTranslateFinite_const (n := n) 1
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact isTranslateFinite_mul (hf i (Finset.mem_insert_self _ _))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem isTranslateFinite_entry (i j : Fin n) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      (κ : Matrix (Fin n) (Fin n) ℂ) i j) := by
  unfold IsTranslateFinite
  set S := Submodule.span ℂ (Set.range fun l : Fin n =>
    fun κ : Matrix.unitaryGroup (Fin n) ℂ => (κ : Matrix (Fin n) (Fin n) ℂ) i l)
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  suffices hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x : Matrix.unitaryGroup (Fin n) ℂ => _) ≤ S from Submodule.finiteDimensional_of_le hle
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  have h : (fun x : Matrix.unitaryGroup (Fin n) ℂ =>
      ((x * k : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j) =
      ∑ l : Fin n, ((k : Matrix (Fin n) (Fin n) ℂ) l j) •
        fun κ : Matrix.unitaryGroup (Fin n) ℂ => (κ : Matrix (Fin n) (Fin n) ℂ) i l := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    change ((x : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)) i j = _
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  change (fun x : Matrix.unitaryGroup (Fin n) ℂ =>
    ((x * k : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j) ∈ S
  rw [h]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem isTranslateFinite_conj_entry (i j : Fin n) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      conj ((κ : Matrix (Fin n) (Fin n) ℂ) i j)) := by
  unfold IsTranslateFinite
  set S := Submodule.span ℂ (Set.range fun l : Fin n =>
    fun κ : Matrix.unitaryGroup (Fin n) ℂ => conj ((κ : Matrix (Fin n) (Fin n) ℂ) i l))
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  suffices hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x : Matrix.unitaryGroup (Fin n) ℂ => _) ≤ S from Submodule.finiteDimensional_of_le hle
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  have h : (fun x : Matrix.unitaryGroup (Fin n) ℂ =>
      conj (((x * k : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)) =
      ∑ l : Fin n, conj ((k : Matrix (Fin n) (Fin n) ℂ) l j) •
        fun κ : Matrix.unitaryGroup (Fin n) ℂ => conj ((κ : Matrix (Fin n) (Fin n) ℂ) i l) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    change conj (((x : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)) i j) = _
    rw [Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_mul, mul_comm]
  change (fun x : Matrix.unitaryGroup (Fin n) ℂ =>
    conj (((x * k : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)) ∈ S
  rw [h]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end TranslateFinite

/-! ## Phase monomials -/

/-- The phase monomial `κ ↦ ∏_l κ_ll^{p⁺_l + a_l} conj(κ_ll)^{p⁻_l + a_l}` on `U(n)`, where
`p⁺ = max(p, 0)` and `p⁻ = max(-p, 0)`. -/
def phaseMonomial (n : ℕ) (p : ℕ → ℤ) (a : ℕ → ℕ) (κ : Matrix.unitaryGroup (Fin n) ℂ) : ℂ :=
  ∏ l : Fin n, ((κ : Matrix (Fin n) (Fin n) ℂ) l l) ^ ((p l).toNat + a l) *
    conj ((κ : Matrix (Fin n) (Fin n) ℂ) l l) ^ ((-(p l)).toNat + a l)

variable {n : ℕ} (p : ℕ → ℤ) (a : ℕ → ℕ)

theorem continuous_phaseMonomial : Continuous (phaseMonomial n p a) := by
  have hentry : ∀ l : Fin n, Continuous fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      (κ : Matrix (Fin n) (Fin n) ℂ) l l := fun l =>
    (continuous_apply l).comp ((continuous_apply l).comp continuous_subtype_val)
  exact continuous_finsetProd _ fun l _ =>
    ((hentry l).pow _).mul ((Complex.continuous_conj.comp (hentry l)).pow _)

theorem finiteDimensional_phaseMonomial :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x => phaseMonomial n p a (x * k))) := by
  have h : IsTranslateFinite (phaseMonomial n p a) := by
    unfold phaseMonomial
    exact isTranslateFinite_prod Finset.univ (fun (l : Fin n) (κ : Matrix.unitaryGroup (Fin n) ℂ) =>
      ((κ : Matrix (Fin n) (Fin n) ℂ) l l) ^ ((p l).toNat + a l) *
        conj ((κ : Matrix (Fin n) (Fin n) ℂ) l l) ^ ((-(p l)).toNat + a l)) fun l _ =>
      isTranslateFinite_mul (isTranslateFinite_pow (isTranslateFinite_entry l l) _)
        (isTranslateFinite_pow (isTranslateFinite_conj_entry l l) _)
  exact h

theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  have h : conj z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp
  exact eq_inv_of_mul_eq_one_left h

theorem principalSeriesCharacter_phase (N : ℕ) (d : Fin N → ℂˣ) :
    principalSeriesCharacter ℂ N χ (fun i => phaseUnit (d i)) =
      ∏ i : Fin N, χ i (phaseUnit (d i)) := by
  rw [principalSeriesCharacter]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_phaseUnit, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]

theorem pow_mul_inv_pow_eq_zpow {u : ℂ} (hu : u ≠ 0) (q : ℤ) (b : ℕ) :
    u ^ (q.toNat + b) * u⁻¹ ^ ((-q).toNat + b) = u ^ q := by
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hu]
  congr 1
  have := Int.toNat_sub_toNat_neg q
  push_cast
  linarith

theorem phaseMonomial_phaseMatrix
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l))
    (d : Fin n → ℂˣ) (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    phaseMonomial n p a (phaseMatrix d * κ) =
      principalSeriesCharacter ℂ n χ (fun i => phaseUnit (d i)) * phaseMonomial n p a κ := by
  rw [principalSeriesCharacter_phase, phaseMonomial, phaseMonomial, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have hentry : ((phaseMatrix d * κ : Matrix.unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) l l =
      ((phaseUnit (d l) : ℂˣ) : ℂ) * (κ : Matrix (Fin n) (Fin n) ℂ) l l := by
    change ((phaseMatrix d : Matrix (Fin n) (Fin n) ℂ) * (κ : Matrix (Fin n) (Fin n) ℂ)) l l = _
    rw [phaseMatrix_val, Matrix.diagonal_mul]
  set u : ℂ := ((phaseUnit (d l) : ℂˣ) : ℂ) with hudef
  set z : ℂ := (κ : Matrix (Fin n) (Fin n) ℂ) l l with hzdef
  have hu : conj u = u⁻¹ := conj_eq_inv_of_norm_eq_one (norm_phaseUnit (d l))
  have hu0 : u ≠ 0 := (phaseUnit (d l)).ne_zero
  have hkey := pow_mul_inv_pow_eq_zpow hu0 (p l) (a l)
  rw [hentry, hp, ← hudef, map_mul, mul_pow, mul_pow, hu]
  calc u ^ ((p l).toNat + a l) * z ^ ((p l).toNat + a l) *
        (u⁻¹ ^ ((-(p l)).toNat + a l) * conj z ^ ((-(p l)).toNat + a l))
      = (u ^ ((p l).toNat + a l) * u⁻¹ ^ ((-(p l)).toNat + a l)) *
          (z ^ ((p l).toNat + a l) * conj z ^ ((-(p l)).toNat + a l)) := by ring
    _ = u ^ (p l) * (z ^ ((p l).toNat + a l) * conj z ^ ((-(p l)).toNat + a l)) := by
        rw [hkey]

/-- The function of the principal series extending the phase monomial. -/
def phaseVector (n : ℕ) (e : ℕ → ℂ) (p : ℕ → ℤ) (a : ℕ → ℕ) : Langlands.GeneralLinear n ℂ → ℂ :=
  extension (GramFormula.shiftedExponent n e) (phaseMonomial n p a)

theorem phaseVector_mem (hχ : IsPhasePower χ e)
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) :
    phaseVector n e p a ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) :=
  extension_mem_kFiniteFunctions e hχ.eq (continuous_phaseMonomial p a)
    (finiteDimensional_phaseMonomial p a) (phaseMonomial_phaseMatrix p a hp)

theorem phaseVector_unitary (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    phaseVector n e p a (Unitary.toUnits κ) = phaseMonomial n p a κ :=
  extension_unitary _ _ _

theorem phaseVector_of_mem {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    phaseVector n e p a k = phaseMonomial n p a ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ := by
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℂ) := Units.ext rfl
  calc phaseVector n e p a k = phaseVector n e p a (Unitary.toUnits
        (⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ : Matrix.unitaryGroup (Fin n) ℂ)) := congrArg _ hku
    _ = _ := phaseVector_unitary p a _

theorem phaseVector_iota {m : ℕ} (e' : ℕ → ℂ) {k : Langlands.GeneralLinear m ℂ}
    (hk : k ∈ unitaryCompact ℂ m) :
    phaseVector (m + 1) e p a (iotaGL k) = phaseVector m e' p a k := by
  rw [phaseVector_of_mem p a (iotaGL_mem_unitaryCompact hk), phaseVector_of_mem p a hk,
    phaseMonomial, phaseMonomial, Fin.prod_univ_castSucc]
  simp only [iotaGL_val, iota_castSucc_castSucc, iota_last_last, Fin.val_castSucc, map_one,
    one_pow, mul_one]

/-! ## The concentrating function `q(y) = |y_{mm}|² / |y_m|²` -/

/-- `q(y) = |y_{mm}|² / ∑_j |y_{mj}|²`, a function of the last row. -/
def qFun {m : ℕ} (y : Langlands.GeneralLinear (m + 1) ℂ) : ℝ :=
  ‖(y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) (Fin.last m)‖ ^ 2 /
    ∑ j, ‖(y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j‖ ^ 2

theorem lastRow_diagonalUnits_mul {m : ℕ} (b : Fin (m + 1) → ℂˣ) (u : upperUnipotent (m + 1) ℂ)
    (y : Langlands.GeneralLinear (m + 1) ℂ) (j : Fin (m + 1)) :
    (((Iwasawa.diagonalUnits b : Langlands.GeneralLinear (m + 1) ℂ) *
      (u : Langlands.GeneralLinear (m + 1) ℂ) * y : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j =
      (b (Fin.last m) : ℂ) * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j := by
  rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_assoc,
    Matrix.diagonal_mul, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [u.2.2 (Fin.last m), one_mul]
  · intro l _ hl
    have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
    rw [show ((u : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      (Fin.last m) l = 0 from u.2.1 hlt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem qFun_mul {m : ℕ} (b : Fin (m + 1) → ℂˣ) (u : upperUnipotent (m + 1) ℂ)
    (y : Langlands.GeneralLinear (m + 1) ℂ) :
    qFun ((Iwasawa.diagonalUnits b : Langlands.GeneralLinear (m + 1) ℂ) *
      (u : Langlands.GeneralLinear (m + 1) ℂ) * y) = qFun y := by
  unfold qFun
  simp only [lastRow_diagonalUnits_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (b (Fin.last m)).ne_zero))

theorem qFun_of_mem {m : ℕ} {κ : Langlands.GeneralLinear (m + 1) ℂ}
    (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    qFun κ = ‖(κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) (Fin.last m)‖ ^ 2 := by
  have h := sqNorm_lastRow (⟨κ, hκ⟩ : unitaryCompact ℂ (m + 1))
  unfold ComplexLastRowIntegral.sqNorm ComplexLastRowIntegral.lastRow at h
  unfold qFun
  rw [show (∑ j, ‖(κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j‖ ^ 2) = 1 from h,
    div_one]

/-- The exponents `a` with `N` added at position `m`. -/
def bump (a : ℕ → ℕ) (m N : ℕ) (l : ℕ) : ℕ := a l + if l = m then N else 0

theorem phaseVector_bump {m : ℕ} (hχ : IsPhasePower χ e)
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l))
    (N : ℕ) (y : Langlands.GeneralLinear (m + 1) ℂ) :
    phaseVector (m + 1) e p (bump a m N) y = (qFun y : ℂ) ^ N * phaseVector (m + 1) e p a y := by
  obtain ⟨b, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary y
  rw [(phaseVector_mem p (bump a m N) hχ hp).1.2 b u κ, (phaseVector_mem p a hχ hp).1.2 b u κ,
    qFun_mul, qFun_of_mem hκ, phaseVector_of_mem _ _ hκ, phaseVector_of_mem _ _ hκ, phaseMonomial,
    phaseMonomial, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have hcs : ∀ l : Fin m, bump a m N (l : ℕ) = a l := fun l => by
    simp [bump, (Fin.isLt l).ne]
  have hlast : bump a m N m = a m + N := by simp [bump]
  simp only [Fin.val_castSucc, Fin.val_last, hcs, hlast]
  set z : ℂ := (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) (Fin.last m)
  have hz : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change _ = ((‖z‖ ^ 2 : ℝ) : ℂ) ^ N * _
  rw [hz]
  ring

theorem lastRow_chartGL_mul_iotaGL {m : ℕ} (x : Fin m → ℂ) (k : Langlands.GeneralLinear m ℂ)
    (j : Fin (m + 1)) :
    ((chartGL x * iotaGL k : Langlands.GeneralLinear (m + 1) ℂ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m) j =
      Fin.lastCases 1 (fun j' => (x ᵥ* (k : Matrix (Fin m) (Fin m) ℂ)) j') j := by
  rw [Units.val_mul, chartGL, JGL_val, iotaGL_val, Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [Jmat]
  · simp [Jmat, Matrix.vecMul, dotProduct]

theorem qFun_chart {m : ℕ} (x : Fin m → ℂ) {k : Langlands.GeneralLinear m ℂ}
    (hk : k ∈ unitaryCompact ℂ m) :
    qFun (chartGL x * iotaGL k) = (1 + ComplexLastRowIntegral.sqNorm x)⁻¹ := by
  unfold qFun
  simp only [lastRow_chartGL_mul_iotaGL, Fin.sum_univ_castSucc, Fin.lastCases_last,
    Fin.lastCases_castSucc, norm_one, one_pow]
  have h := ComplexLastRowIntegral.sqNorm_vecMul
    (ComplexLastRowIntegral.mul_conjTranspose_eq_one ⟨k, hk⟩) x
  unfold ComplexLastRowIntegral.sqNorm at h ⊢
  rw [h]
  ring

/-! ## The approximate identity -/

theorem bernoulli_pow {s : ℝ} (hs : 0 ≤ s) {N₀ N : ℕ} (h0 : 0 < N₀) (hN : N₀ ≤ N) :
    (1 + s / N₀) ^ N₀ ≤ (1 + s / N) ^ N := by
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast h0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le h0 hN
  have hp : (1 : ℝ) ≤ (N : ℝ) / N₀ := by
    rw [le_div_iff₀ hN0, one_mul]
    exact_mod_cast hN
  have hs' : (-1 : ℝ) ≤ s / N := by
    have : 0 ≤ s / N := div_nonneg hs hNpos.le
    linarith
  have hb := one_add_mul_self_le_rpow_one_add hs' hp
  have h1 : (N : ℝ) / N₀ * (s / N) = s / N₀ := by field_simp
  rw [h1] at hb
  have hbase : 0 ≤ 1 + s / N := by positivity
  calc (1 + s / N₀) ^ N₀ ≤ ((1 + s / N) ^ ((N : ℝ) / N₀)) ^ N₀ :=
        pow_le_pow_left₀ (by positivity) hb N₀
    _ = (1 + s / N) ^ N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase, div_mul_cancel₀ _ hN0.ne',
          Real.rpow_natCast]

theorem integrable_inv_one_add_div_pow (m : ℕ) :
    Integrable fun y : Fin m → ℂ =>
      ((1 + ComplexLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ := by
  have hN0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hcont : Continuous fun y : Fin m → ℂ =>
      ((1 + ComplexLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ := by
    refine Continuous.inv₀ ((continuous_const.add
      (ComplexLastRowIntegral.continuous_sqNorm.div_const _)).pow _) fun y => (pow_pos (by
        have := ComplexLastRowIntegral.sqNorm_nonneg y
        positivity) _).ne'
  refine (ComplexLastRowIntegral.integrable_chartWeight.const_mul
    (((m + 1 : ℕ) : ℝ) ^ (m + 1))).mono' hcont.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have hs0 := ComplexLastRowIntegral.sqNorm_nonneg y
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity) _)),
    ComplexLastRowIntegral.chartWeight]
  have h1 : (1 + ComplexLastRowIntegral.sqNorm y) / ((m + 1 : ℕ) : ℝ) ≤
      1 + ComplexLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hN0, add_mul, div_mul_cancel₀ _ hN0.ne', one_mul]
    have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    linarith
  have h2 : ((1 + ComplexLastRowIntegral.sqNorm y) / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) ≤
      (1 + ComplexLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  calc ((1 + ComplexLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹
      ≤ (((1 + ComplexLastRowIntegral.sqNorm y) / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ :=
        inv_anti₀ (pow_pos (by positivity) _) h2
    _ = ((m + 1 : ℕ) : ℝ) ^ (m + 1) * ((1 + ComplexLastRowIntegral.sqNorm y) ^ (m + 1))⁻¹ := by
        rw [div_pow, inv_div, div_eq_mul_inv]

theorem norm_chart_le_of_mem {m : ℕ} (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    {H : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hH : H ∈ principalSeries ℂ (m + 1) χ) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℂ (m + 1), ‖H k‖ ≤ C) (x : Fin m → ℂ)
    {κ : Langlands.GeneralLinear (m + 1) ℂ} (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    ‖H (chartGL x * κ)‖ ≤ C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℂ (m + 1)).one_mem)
  refine (norm_le_of_mem_principalSeries hχ he hH hC x hκ).trans ?_
  refine mul_le_of_le_one_right hC0 (Finset.prod_le_one₀ (fun l _ =>
    (Real.rpow_pos_of_pos (by positivity) _).le) fun l _ =>
      Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) ?_)
  have := chartExponent_lt he l
  linarith

theorem norm_ofReal_inv {c : ℝ} (hc : 0 < c) : ‖(((c⁻¹ : ℝ) : ℂ))‖ = c⁻¹ := by
  simp [abs_of_pos hc]

theorem integral_scale {m : ℕ} (f : (Fin m → ℂ) → ℂ) {c : ℝ} (hc : 0 < c) :
    ((c ^ (2 * m) : ℝ) : ℂ) * ∫ x, f x = ∫ y, f (((c⁻¹ : ℝ) : ℂ) • y) := by
  have hs : ((c⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_ofReal_inv hc]
    exact (inv_pos.mpr hc).ne'
  rw [ComplexLastRowIntegral.integral_comp_complex_smul f hs, Complex.real_smul,
    norm_ofReal_inv hc, inv_pow, inv_inv]

theorem sqNorm_scale {k : ℕ} (y : Fin k → ℂ) {c : ℝ} (hc : 0 < c) :
    ComplexLastRowIntegral.sqNorm (((c⁻¹ : ℝ) : ℂ) • y) =
      ComplexLastRowIntegral.sqNorm y / c ^ 2 := by
  rw [ComplexLastRowIntegral.sqNorm_smul, norm_ofReal_inv hc, inv_pow, inv_mul_eq_div]

/-- **Approximate identity.** With `N' = N + m + 1`,
`N'^m ∫_{ℂ^m} (1 + |x|²)^{-N'} H(J(x,1) ι(k)) dx → (∫ e^{-|y|²} dy) H(ι(k))`. -/
theorem tendsto_concentrate {m : ℕ} (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    {H : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hH : H ∈ principalSeries ℂ (m + 1) χ)
    {k : Langlands.GeneralLinear m ℂ} (hk : k ∈ unitaryCompact ℂ m) :
    Tendsto (fun N : ℕ => ((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ (2 * m) : ℝ) : ℂ) *
        ∫ x : Fin m → ℂ, ((((1 + ComplexLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
          H (chartGL x * iotaGL k)) atTop
      (𝓝 ((∫ y : Fin m → ℂ, ComplexLastRowIntegral.gaussian y : ℝ) * H (iotaGL k))) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hH.1.continuous
  have hκ := iotaGL_mem_unitaryCompact hk
  have hNpos : 0 < m + 1 := Nat.succ_pos m
  -- the substituted integrands
  set g : ℕ → (Fin m → ℂ) → ℂ := fun N y =>
    ((((1 + ComplexLastRowIntegral.sqNorm y / ((N + (m + 1) : ℕ) : ℝ)) ^ (N + (m + 1)))⁻¹ : ℝ) :
      ℂ) * H (chartGL ((((Real.sqrt ((N + (m + 1) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y) * iotaGL k)
    with hg
  have hsub : ∀ N : ℕ, ((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ (2 * m) : ℝ) : ℂ) *
      ∫ x : Fin m → ℂ, ((((1 + ComplexLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
        H (chartGL x * iotaGL k) = ∫ y, g N y := by
    intro N
    have hpos : 0 < ((N + (m + 1) : ℕ) : ℝ) := by positivity
    have hsq : 0 < Real.sqrt ((N + (m + 1) : ℕ) : ℝ) := Real.sqrt_pos.mpr hpos
    rw [integral_scale _ hsq]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hg]
    rw [sqNorm_scale y hsq, Real.sq_sqrt hpos.le]
  refine (tendsto_congr hsub).mpr ?_
  set bound : (Fin m → ℂ) → ℝ := fun y =>
    C * ((1 + ComplexLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ with hbound
  have hbi : Integrable bound := (integrable_inv_one_add_div_pow m).const_mul C
  have hlimit : (∫ y : Fin m → ℂ, ComplexLastRowIntegral.gaussian y : ℝ) * H (iotaGL k) =
      ∫ y : Fin m → ℂ, ((Real.exp (-ComplexLastRowIntegral.sqNorm y) : ℝ) : ℂ) *
        H (iotaGL k) := by
    rw [integral_mul_const, integral_complex_ofReal]
    rfl
  rw [hlimit]
  refine tendsto_integral_of_dominated_convergence bound (fun N => ?_) hbi
    (fun N => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    simp only [hg]
    refine Continuous.mul (Complex.continuous_ofReal.comp (Continuous.inv₀
      ((continuous_const.add (ComplexLastRowIntegral.continuous_sqNorm.div_const _)).pow _)
        fun y => (pow_pos (by
          have := ComplexLastRowIntegral.sqNorm_nonneg y
          positivity) _).ne'))
      (hH.1.continuous.comp ((continuous_chartGL.comp (continuous_const_smul _)).mul
        continuous_const))
  · simp only [hg, hbound]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (by
      have := ComplexLastRowIntegral.sqNorm_nonneg y
      positivity) _)), mul_comm C]
    have hs0 := ComplexLastRowIntegral.sqNorm_nonneg y
    refine mul_le_mul (inv_anti₀ (pow_pos (by positivity) _)
      (bernoulli_pow hs0 hNpos (by omega))) (norm_chart_le_of_mem hχ he hH hC _ hκ)
      (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg (by positivity) _))
  · simp only [hg]
    have hshift : Tendsto (fun N : ℕ => N + (m + 1)) atTop atTop := tendsto_add_atTop_nat (m + 1)
    have h1 : Tendsto (fun N : ℕ => (1 + ComplexLastRowIntegral.sqNorm y /
        ((N + (m + 1) : ℕ) : ℝ)) ^ (N + (m + 1))) atTop
        (𝓝 (Real.exp (ComplexLastRowIntegral.sqNorm y))) :=
      (Real.tendsto_one_add_div_pow_exp _).comp hshift
    have h2 := h1.inv₀ (Real.exp_ne_zero _)
    rw [← Real.exp_neg] at h2
    have h3 : Tendsto (fun N : ℕ => (Real.sqrt ((N + (m + 1) : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
      have h4 : Tendsto (fun N : ℕ => Real.sqrt ((N + (m + 1) : ℕ) : ℝ)) atTop atTop :=
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).comp hshift
      exact tendsto_inv_atTop_zero.comp h4
    have h3' : Tendsto (fun N : ℕ => (((Real.sqrt ((N + (m + 1) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)) atTop
        (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp h3
      simpa [Function.comp_def] using this
    have h5 : Tendsto (fun N : ℕ => (((Real.sqrt ((N + (m + 1) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y) atTop
        (𝓝 0) := by
      simpa using h3'.smul_const y
    have hcont : Continuous fun z : Fin m → ℂ => H (chartGL z * iotaGL k) :=
      hH.1.continuous.comp (continuous_chartGL.mul continuous_const)
    have h6 := (hcont.tendsto 0).comp h5
    simp only [Function.comp_def, chartGL_zero, one_mul] at h6
    exact ((Complex.continuous_ofReal.tendsto _).comp h2).mul h6

theorem norm_concentrate_le {m : ℕ} (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    {H : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hH : H ∈ principalSeries ℂ (m + 1) χ) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℂ (m + 1), ‖H k‖ ≤ C) (N : ℕ)
    {k : Langlands.GeneralLinear m ℂ} (hk : k ∈ unitaryCompact ℂ m) :
    ‖((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ (2 * m) : ℝ) : ℂ) *
        ∫ x : Fin m → ℂ, ((((1 + ComplexLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
          H (chartGL x * iotaGL k)‖ ≤
      ∫ y : Fin m → ℂ, C * ((1 + ComplexLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^
        (m + 1))⁻¹ := by
  have hκ := iotaGL_mem_unitaryCompact hk
  have hpos : 0 < ((N + (m + 1) : ℕ) : ℝ) := by positivity
  have hsq : 0 < Real.sqrt ((N + (m + 1) : ℕ) : ℝ) := Real.sqrt_pos.mpr hpos
  rw [integral_scale _ hsq]
  refine norm_integral_le_of_norm_le ((integrable_inv_one_add_div_pow m).const_mul C)
    (ae_of_all _ fun y => ?_)
  have hs0 := ComplexLastRowIntegral.sqNorm_nonneg y
  rw [sqNorm_scale y hsq, Real.sq_sqrt hpos.le, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity) _)), mul_comm C]
  exact mul_le_mul (inv_anti₀ (pow_pos (by positivity) _)
    (bernoulli_pow hs0 (Nat.succ_pos m) (by omega))) (norm_chart_le_of_mem hχ he hH hC _ hκ)
    (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg (by positivity) _))

/-! ## Nonvanishing -/

theorem shiftChar_phase (l : ℕ) (z : ℂˣ) : shiftChar χ l (phaseUnit z) = χ l (phaseUnit z) := by
  simp [shiftChar, norm_phaseUnit]

theorem phaseVector_zero_one (e : ℕ → ℂ) (p : ℕ → ℤ) (a : ℕ → ℕ) :
    phaseVector 0 e p a 1 = 1 := by
  rw [phaseVector_of_mem p a (unitaryCompact ℂ 0).one_mem]
  simp [phaseMonomial]

/-- **The Jacquet integral does not vanish.** For strictly dominant phase-power characters `χ`
with `χ_l(u) = u^{p_l}` on the unit circle, some phase vector of the principal series has
nonzero Jacquet integral. -/
theorem exists_jacquet_phaseVector_ne_zero : ∀ (n : ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ},
    IsPhasePower χ e → IsStrictlyDominant e (n - 1) → ∀ {p : ℕ → ℤ},
    (∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) →
    ∃ a : ℕ → ℕ, jacquet n (phaseVector n e p a) ≠ 0
  | 0, χ, e, _, _, p, _ => ⟨0, by
      change phaseVector 0 e p 0 1 ≠ 0
      rw [phaseVector_zero_one]
      exact one_ne_zero⟩
  | m + 1, χ, e, hχ, he, p, hp => by
      have he' : IsStrictlyDominant e m := by simpa using he
      have hp' : ∀ (l : ℕ) (z : ℂˣ), shiftChar χ l (phaseUnit z) =
          ((phaseUnit z : ℂˣ) : ℂ) ^ (p l) := fun l z => by rw [shiftChar_phase, hp]
      obtain ⟨a, ha⟩ := exists_jacquet_phaseVector_ne_zero m hχ.shift
        (isStrictlyDominant_shift he') hp'
      have hH := phaseVector_mem (n := m + 1) p a hχ hp
      obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hH.1.1.continuous
      set c : ℕ → ℂ := fun N => ((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ (2 * m) : ℝ) : ℂ)
        with hcdef
      set F : ℕ → Langlands.GeneralLinear (m + 1) ℂ → ℂ := fun N =>
        c N • phaseVector (m + 1) e p (bump a m (N + (m + 1))) with hFdef
      have hF : ∀ N, F N ∈ kFiniteFunctions (principalSeries ℂ (m + 1) χ)
          (unitaryCompact ℂ (m + 1)) := fun N =>
        Submodule.smul_mem _ _ (phaseVector_mem _ _ hχ hp)
      have hval : ∀ N, ∀ k ∈ unitaryCompact ℂ m, jacquetStep (F N) k =
          c N * ∫ x : Fin m → ℂ,
            ((((1 + ComplexLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
              phaseVector (m + 1) e p a (chartGL x * iotaGL k) := by
        intro N k hk
        simp only [hFdef, jacquetStep, Pi.smul_apply, smul_eq_mul]
        rw [integral_const_mul]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [phaseVector_bump p a hχ hp, qFun_chart x hk]
        push_cast
        rw [inv_pow]
      set cG : ℂ := ((∫ y : Fin m → ℂ, ComplexLastRowIntegral.gaussian y : ℝ) : ℂ) with hcG
      have hlim := tendsto_jacquet m hχ.shift (isStrictlyDominant_shift he')
        (f := fun N => jacquetStep (F N)) (f₀ := cG • phaseVector m (fun l => e l - 1 / 2) p a)
        (fun N => jacquetStep_mem hχ he' (hF N))
        (Submodule.smul_mem _ _ (phaseVector_mem p a hχ.shift hp'))
        (C := ∫ y : Fin m → ℂ, C * ((1 + ComplexLastRowIntegral.sqNorm y /
          ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹)
        (fun N k hk => by
          rw [hval N k hk]
          exact norm_concentrate_le hχ he' hH.1 hC N hk)
        (fun k hk => by
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [← phaseVector_iota (e := e) p a (fun l => e l - 1 / 2) hk]
          exact (tendsto_congr fun N => hval N k hk).mpr (tendsto_concentrate hχ he' hH.1 hk))
      have hne : jacquet m (cG • phaseVector m (fun l => e l - 1 / 2) p a) ≠ 0 := by
        rw [jacquet_smul]
        refine mul_ne_zero ?_ ha
        rw [hcG]
        exact_mod_cast (ComplexLastRowIntegral.integral_gaussian_pos (m := m)).ne'
      obtain ⟨N, hN⟩ := (hlim.eventually (isOpen_ne.mem_nhds hne)).exists
      refine ⟨bump a m (N + (m + 1)), fun h0 => hN ?_⟩
      have h1 : jacquet (m + 1) (F N) =
          c N * jacquet (m + 1) (phaseVector (m + 1) e p (bump a m (N + (m + 1)))) :=
        jacquet_smul _ _ _
      change jacquet (m + 1) (F N) = 0
      rw [h1, h0, mul_zero]

/-- The Jacquet integral is a nonzero functional on the `U(n)`-finite principal series. -/
theorem exists_jacquet_ne_zero {n : ℕ} (hχ : IsPhasePower χ e)
    (he : IsStrictlyDominant e (n - 1)) {p : ℕ → ℤ}
    (hp : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = ((phaseUnit z : ℂˣ) : ℂ) ^ (p l)) :
    ∃ f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n), jacquet n f ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_jacquet_phaseVector_ne_zero n hχ he hp
  exact ⟨_, phaseVector_mem p a hχ hp, ha⟩

end ComplexJacquetNonvanishing

/-- **The Jacquet integral of a strictly dominant complex principal series is nonzero.** Let
`χ_0, …, χ_{n-1}` be characters of `ℂˣ` with `χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`,
`χ_l(u) = u^{p_l}` for `u = z/|z|` on the unit circle (`p_l ∈ ℤ`) and
`Re e_0 > ⋯ > Re e_{n-1}`. Then some `U(n)`-finite function of the smooth principal series of `χ`
has nonzero Jacquet integral `Λ_n` (`ComplexJacquetDual.jacquet`). -/
def ComplexJacquetNonvanishingStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ) (p : ℕ → ℤ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), χ l (ComplexGramFormula.phaseUnit z) =
      ((ComplexGramFormula.phaseUnit z : ℂˣ) : ℂ) ^ (p l)) →
    (∀ l : ℕ, l + 1 < n → (e (l + 1)).re < (e l).re) →
    ∃ f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n),
      ComplexJacquetDual.jacquet n f ≠ 0

theorem complexJacquetNonvanishing : ComplexJacquetNonvanishingStatement := by
  intro n χ e p heq hone hp hdom
  have hχ : ComplexPartialJacquet.IsPhasePower χ e :=
    ⟨heq, hone, fun l z => by rw [hp, norm_zpow, ComplexGramFormula.norm_phaseUnit, _root_.one_zpow]⟩
  exact ComplexJacquetNonvanishing.exists_jacquet_ne_zero hχ (fun l hl => hdom l (by omega)) hp

end Langlands.Archimedean
