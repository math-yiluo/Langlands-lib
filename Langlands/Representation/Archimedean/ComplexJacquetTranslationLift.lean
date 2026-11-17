import Langlands.Representation.Archimedean.ComplexJacquetTranslationMinors
import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Langlands.Representation.Archimedean.ComplexJacquetNonvanishing
import Langlands.Representation.Archimedean.ComplexTemperedComplement

/-!
# Tuples of principal-series functions indexed by `k`-subsets

The `(𝔤, K)`-module `X(d) ⊗ Λ^k` as tuples `(f_T)` of `U(n)`-finite principal-series functions,
its components `π_S f (g) = ∑_T m_{S T}(g) f_T(g)` along the minors `m(g)` of `g` (or of `ḡ`),
lifts of functions of the shifted principal series `X(d + e_S)`, and the decomposition of every
tuple into lifts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff Manifold ComplexConjugate

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.JacquetTranslation

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n k : ℕ}

/-! ## The shifted characters -/

/-- `z` (holomorphic, `anti = false`) or `z̄` (antiholomorphic, `anti = true`). -/
def fac (anti : Bool) (z : ℂ) : ℂ := if anti then conj z else z

/-- The weight shift: `1` (holomorphic) or `-1` (antiholomorphic). -/
def eps (anti : Bool) : ℤ := if anti then -1 else 1

theorem borelFactor_shift (anti : Bool) (l : ℤ) (α : ℂ) {z : ℂ} (hz : z ≠ 0) :
    borelFactor (l + eps anti) (α + 1) z = borelFactor l α z * fac anti z := by
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hdiv : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz hr
  have hexp : Complex.exp (Real.log ‖z‖ : ℂ) = (‖z‖ : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hz)]
  rw [borelFactor, borelFactor, zpow_add₀ hdiv, mul_add, mul_one, Complex.exp_add, hexp]
  cases anti
  · simp only [eps, fac, Bool.false_eq_true, if_false, zpow_one]
    field_simp
  · simp only [eps, fac, if_true]
    have hconj : conj z = (‖z‖ : ℂ) ^ 2 / z := by
      rw [eq_div_iff hz, mul_comm, Complex.mul_conj']
    rw [hconj, zpow_neg_one, inv_div]
    field_simp

/-- The characters `d` with the holomorphic (or antiholomorphic) coordinate raised by `1` at the
positions of `S`. -/
def shiftChar (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Finset (Fin n)) :
    Fin n → ComplexCharacterData :=
  fun j => if j ∈ S then characterOfParams ((d j).weight + eps anti) ((d j).exponent + 1 / 2)
    else d j

theorem shiftChar_weight (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Finset (Fin n))
    (j : Fin n) :
    (shiftChar anti d S j).weight = (d j).weight + if j ∈ S then eps anti else 0 := by
  by_cases hj : j ∈ S <;> simp [shiftChar, hj]

theorem shiftChar_exponent (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Finset (Fin n))
    (j : Fin n) :
    (shiftChar anti d S j).exponent = (d j).exponent + if j ∈ S then (1 / 2 : ℂ) else 0 := by
  by_cases hj : j ∈ S <;> simp [shiftChar, hj]

/-- The principal-series character of the shifted characters. -/
theorem principalSeriesCharacter_shift (anti : Bool) (d : Fin n → ComplexCharacterData)
    (S : Finset (Fin n)) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn (shiftChar anti d S))) a =
      principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d)) a *
        ∏ r ∈ S, fac anti (a r) := by
  rw [principalSeriesCharacter_ofFn, principalSeriesCharacter_ofFn]
  have hj : ∀ j : Fin n, borelFactor (shiftChar anti d S j).weight
      (2 * (shiftChar anti d S j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ)) (a j) =
      borelFactor (d j).weight (2 * (d j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ)) (a j) *
        (if j ∈ S then fac anti (a j) else 1) := by
    intro j
    by_cases hjS : j ∈ S
    · simp only [shiftChar, hjS, if_true, characterOfParams_weight, characterOfParams_exponent]
      rw [show 2 * ((d j).exponent + 1 / 2) + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ) =
        (2 * (d j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ)) + 1 by ring]
      exact borelFactor_shift anti _ _ (a j).ne_zero
    · simp [shiftChar, hjS]
  rw [Finset.prod_congr rfl (fun j _ => hj j), Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter]

/-! ## Upper triangular matrices `diag(a) u` -/

theorem borel_entry_lt (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) {i j : Fin n} (h : j < i) :
    (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * (u : Langlands.GeneralLinear n ℂ) :
      Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
  rw [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.diagonal_mul,
    UpperUnipotent.entry_eq_zero u h, mul_zero]

theorem borel_entry_diag (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (i : Fin n) :
    (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * (u : Langlands.GeneralLinear n ℂ) :
      Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = a i := by
  rw [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]
  simp

theorem phi_borel_entry_lt (anti : Bool) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) {i j : Fin n}
    (h : j < i) :
    phi anti (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
  have h0 := borel_entry_lt a u h
  cases anti
  · simpa [phi] using h0
  · simp only [phi, ite_true, Matrix.map_apply]
    rw [h0, map_zero]

theorem mm_borel_self (anti : Bool) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (S : Sub n k) :
    (mm anti (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Sub n k) (Sub n k) ℂ) S S = ∏ r ∈ (S : Finset (Fin n)), fac anti (a r) := by
  rw [mm, minorMat_upper_self (fun i j h => phi_borel_entry_lt anti a u h)]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  cases anti <;> simp [phi, fac, borel_entry_diag]

theorem mm_borel_eq_zero (anti : Bool) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    {S S' : Sub n k} (hle : wt S ≤ wt S') (hne : S' ≠ S) :
    (mm anti (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Sub n k) (Sub n k) ℂ) S' S = 0 := by
  by_contra h
  have := minorMat_upper_ne_zero (fun i j h => phi_borel_entry_lt anti a u h) h
  exact hne (this.2 (le_antisymm this.1 hle))

/-! ## Tuples and their components -/

/-- The `U(n)`-finite functions of the principal series of `d`. -/
abbrev KX (d : Fin n → ComplexCharacterData) : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n)

/-- The component `π_S F (g) = ∑_T m_{S T}(g) F_T(g)` of a tuple `F`. -/
def piS (anti : Bool) (F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ) (S : Sub n k) :
    Langlands.GeneralLinear n ℂ → ℂ :=
  fun g => ∑ T, (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S T * F T g

/-- The components under left multiplication by `diag(a) u`. -/
theorem piS_borel (anti : Bool) {d : Fin n → ComplexCharacterData}
    {F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ}
    (hF : ∀ T, F T ∈ principalSeries ℂ n (complexPositionCharacter (List.ofFn d)))
    (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (S : Sub n k) (g : Langlands.GeneralLinear n ℂ) :
    piS anti F S ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g) =
      principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d)) a *
        ∑ U, (mm anti (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
          (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
            Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S U * piS anti F U g := by
  simp only [piS]
  rw [Units.val_mul (_ * _) g, mm_mul]
  simp only [(hF _).2 a u g, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun U _ => Finset.sum_congr rfl (fun T _ => ?_))
  ring

/-! ## Translate-finite functions on `U(n)` -/

open ComplexJacquetNonvanishing in
theorem isTF_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix.unitaryGroup (Fin n) ℂ → ℂ)
    (hf : ∀ i ∈ s, IsTranslateFinite (f i)) : IsTranslateFinite (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTranslateFinite_const (n := n) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact isTranslateFinite_add (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

open ComplexJacquetNonvanishing in
/-- Minors of a matrix with translate-finite entries are translate-finite. -/
theorem isTF_minorMat {M : Matrix.unitaryGroup (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ a b, IsTranslateFinite (fun κ => M κ a b)) (S T : Sub n k) :
    IsTranslateFinite (fun κ => (minorMat (M κ) : Matrix (Sub n k) (Sub n k) ℂ) S T) := by
  simp only [minorMat_apply, Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  refine isTF_sum _ _ (fun σ _ => isTranslateFinite_mul (isTranslateFinite_const _)
    (isTranslateFinite_prod _ _ (fun i _ => hM _ _)))

open ComplexJacquetNonvanishing in
theorem isTF_phi (anti : Bool) (a b : Fin n) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      phi anti (κ : Matrix (Fin n) (Fin n) ℂ) a b) := by
  cases anti
  · simpa [phi] using isTranslateFinite_entry a b
  · simpa [phi] using isTranslateFinite_conj_entry a b

open ComplexJacquetNonvanishing in
theorem isTF_phi_star (anti : Bool) (a b : Fin n) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      phi anti (star (κ : Matrix (Fin n) (Fin n) ℂ)) a b) := by
  cases anti
  · simpa [phi, Matrix.star_apply] using isTranslateFinite_conj_entry b a
  · simpa [phi, Matrix.star_apply] using isTranslateFinite_entry b a

open ComplexJacquetNonvanishing in
/-- The restriction to `U(n)` of a `U(n)`-finite function is translate-finite. -/
theorem isTF_restrict {V : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ)}
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ kFiniteFunctions V (unitaryCompact ℂ n)) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ => h (Unitary.toUnits κ)) := by
  unfold IsTranslateFinite
  set W := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
      (k : Langlands.GeneralLinear n ℂ) h) with hW
  have hWfin : FiniteDimensional ℂ W := (mem_kFiniteVectors_iff _ _ _).mp hh.2
  let res : (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℂ → ℂ) :=
    { toFun := fun f x => f (Unitary.toUnits x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
      fun x : Matrix.unitaryGroup (Fin n) ℂ => h (Unitary.toUnits (x * k))) ≤ W.map res := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩, funext fun x => ?_⟩
    change h (Unitary.toUnits x * Unitary.toUnits k) = h (Unitary.toUnits (x * k))
    rw [map_mul]
  exact Submodule.finiteDimensional_of_le hle

/-! ## Lifts -/

open ComplexPrincipalSeriesExtension ComplexGramFormula

/-- The function on `U(n)` defining the `T`-component of the lift of `h` from position `S`:
`κ ↦ h(κ) m_{T S}(κ⁻¹)`. -/
def liftK (anti : Bool) (h : Langlands.GeneralLinear n ℂ → ℂ) (S T : Sub n k)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) : ℂ :=
  h (Unitary.toUnits κ) *
    (mm anti (star (κ : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Sub n k) (Sub n k) ℂ) T S

theorem fac_mul_fac_conj (anti : Bool) {z : ℂ} (hz : ‖z‖ = 1) :
    fac anti z * fac anti (conj z) = 1 := by
  have h1 : z * conj z = 1 := by
    rw [Complex.mul_conj', hz]; simp
  cases anti
  · simpa [fac] using h1
  · simp only [fac, ite_true, Complex.conj_conj]
    rw [mul_comm]; exact h1

theorem mm_star_phaseMatrix_mul (anti : Bool) (a : Fin n → ℂˣ)
    (κ : Matrix.unitaryGroup (Fin n) ℂ) (T S : Sub n k) :
    (mm anti (star ((phaseMatrix a * κ : Matrix.unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ)) : Matrix (Sub n k) (Sub n k) ℂ) T S =
      (mm anti (star (κ : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Sub n k) (Sub n k) ℂ) T S *
        ∏ r ∈ (S : Finset (Fin n)), fac anti (conj ((phaseUnit (a r) : ℂˣ) : ℂ)) := by
  have hstar : star ((phaseMatrix a * κ : Matrix.unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) = star (κ : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i => conj ((phaseUnit (a i) : ℂˣ) : ℂ)) := by
    rw [Submonoid.coe_mul, StarMul.star_mul, phaseMatrix_val]
    congr 1
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    rfl
  have hphi : phi anti (Matrix.diagonal (fun i => conj ((phaseUnit (a i) : ℂˣ) : ℂ))) =
      Matrix.diagonal (fun i => fac anti (conj ((phaseUnit (a i) : ℂˣ) : ℂ))) := by
    cases anti
    · simp [phi, fac]
    · ext i j
      by_cases hij : i = j <;> simp [phi, fac, hij]
  rw [hstar, mm_mul, Matrix.mul_apply]
  simp only [mm] at *
  rw [hphi]
  simp only [minorMat_diagonal, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem liftK_phaseMatrix_mul (anti : Bool) {d : Fin n → ComplexCharacterData} (S T : Sub n k)
    {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ n (complexPositionCharacter
      (List.ofFn (shiftChar anti d (S : Finset (Fin n))))))
    (a : Fin n → ℂˣ) (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    liftK anti h S T (phaseMatrix a * κ) =
      principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d))
        (fun i => phaseUnit (a i)) * liftK anti h S T κ := by
  simp only [liftK]
  rw [ComplexPartialJacquet.phaseMatrix_toUnits, hh.2, principalSeriesCharacter_shift,
    mm_star_phaseMatrix_mul]
  have hprod : (∏ r ∈ (S : Finset (Fin n)), fac anti ((phaseUnit (a r) : ℂˣ) : ℂ)) *
      ∏ r ∈ (S : Finset (Fin n)), fac anti (conj ((phaseUnit (a r) : ℂˣ) : ℂ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun r _ => fac_mul_fac_conj anti (norm_phaseUnit (a r)))
  calc _ = principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d))
        (fun i => phaseUnit (a i)) * (h (Unitary.toUnits κ) *
          (mm anti (star (κ : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Sub n k) (Sub n k) ℂ) T S) *
        ((∏ r ∈ (S : Finset (Fin n)), fac anti ((phaseUnit (a r) : ℂˣ) : ℂ)) *
          ∏ r ∈ (S : Finset (Fin n)), fac anti (conj ((phaseUnit (a r) : ℂˣ) : ℂ))) := by ring
    _ = _ := by rw [hprod, mul_one]

open ComplexJacquetNonvanishing in
theorem isTF_mm_star (anti : Bool) (T S : Sub n k) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      (mm anti (star (κ : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Sub n k) (Sub n k) ℂ) T S) :=
  isTF_minorMat (fun a b => isTF_phi_star anti a b) T S

open ComplexJacquetNonvanishing in
theorem isTF_mm (anti : Bool) (S T : Sub n k) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      (mm anti (κ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S T) :=
  isTF_minorMat (fun a b => isTF_phi anti a b) S T

open ComplexJacquetNonvanishing in
/-- The lift exists: a `U(n)`-finite function of `X(d)` with values `liftK` on `U(n)`. -/
theorem exists_lift (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (T : Sub n k) :
    ∃ f ∈ KX d, ∀ κ, f (Unitary.toUnits κ) = liftK anti h S T κ := by
  refine complexPrincipalSeriesExtension n (List.ofFn d) _ ?_ ?_
    (liftK_phaseMatrix_mul anti S T hh.1)
  · exact (hh.1.1.continuous.comp continuous_unitary_toUnits).mul
      ((contDiff_mm anti T S).continuous.comp (continuous_star.comp continuous_subtype_val))
  · have hL : IsTranslateFinite (liftK anti h S T) :=
      isTranslateFinite_mul (isTF_restrict hh) (isTF_mm_star anti T S)
    exact hL

open Classical in
/-- The lift of `h` from position `S`: the `T`-component is the function of `X(d)` with values
`h(κ) m_{T S}(κ⁻¹)` on `U(n)`. -/
def lift (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k)
    (h : Langlands.GeneralLinear n ℂ → ℂ) (T : Sub n k) : Langlands.GeneralLinear n ℂ → ℂ :=
  if hh : h ∈ KX (shiftChar anti d (S : Finset (Fin n))) then
    Classical.choose (exists_lift anti d S hh T) else 0

theorem lift_mem (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (T : Sub n k) : lift anti d S h T ∈ KX d := by
  rw [lift, dif_pos hh]
  exact (Classical.choose_spec (exists_lift anti d S hh T)).1

theorem lift_unitary (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (T : Sub n k) (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    lift anti d S h T (Unitary.toUnits κ) = liftK anti h S T κ := by
  rw [lift, dif_pos hh]
  exact (Classical.choose_spec (exists_lift anti d S hh T)).2 κ

theorem toUnits_of_mem {g : Langlands.GeneralLinear n ℂ} (hg : g ∈ unitaryCompact ℂ n) :
    g = Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℂ), hg⟩ : Matrix.unitaryGroup (Fin n) ℂ) :=
  Units.ext rfl

/-- Two functions of the same principal series that agree on `U(n)` are equal. -/
theorem eq_of_eq_unitary {χ : ℕ → ℂˣ → ℂ} {f g : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ principalSeries ℂ n χ) (hg : g ∈ principalSeries ℂ n χ)
    (h : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ, f (Unitary.toUnits κ) = g (Unitary.toUnits κ)) :
    f = g :=
  eq_of_eqOn_unitary hf hg (fun k hk => by rw [toUnits_of_mem hk]; exact h _)

theorem lift_add (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k)
    {h₁ h₂ : Langlands.GeneralLinear n ℂ → ℂ}
    (hh₁ : h₁ ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (hh₂ : h₂ ∈ KX (shiftChar anti d (S : Finset (Fin n)))) (T : Sub n k) :
    lift anti d S (h₁ + h₂) T = lift anti d S h₁ T + lift anti d S h₂ T := by
  have hh := Submodule.add_mem _ hh₁ hh₂
  refine eq_of_eq_unitary (lift_mem anti d S hh T).1
    (Submodule.add_mem _ (lift_mem anti d S hh₁ T).1 (lift_mem anti d S hh₂ T).1) (fun κ => ?_)
  rw [Pi.add_apply, lift_unitary anti d S hh, lift_unitary anti d S hh₁, lift_unitary anti d S hh₂]
  simp only [liftK, Pi.add_apply, add_mul]

theorem lift_smul (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k) (c : ℂ)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (T : Sub n k) :
    lift anti d S (c • h) T = c • lift anti d S h T := by
  have hc := Submodule.smul_mem _ c hh
  refine eq_of_eq_unitary (lift_mem anti d S hc T).1
    (Submodule.smul_mem _ c (lift_mem anti d S hh T).1) (fun κ => ?_)
  rw [Pi.smul_apply, lift_unitary anti d S hc, lift_unitary anti d S hh]
  simp only [liftK, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem unitary_mul_star (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    (κ : Matrix (Fin n) (Fin n) ℂ) * star (κ : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp κ.2

theorem star_mul_unitary (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    star (κ : Matrix (Fin n) (Fin n) ℂ) * (κ : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp κ.2

/-- The components of a lift on `U(n)`. -/
theorem piS_lift_unitary (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (U : Sub n k) (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    piS anti (lift anti d S h) U (Unitary.toUnits κ) =
      if U = S then h (Unitary.toUnits κ) else 0 := by
  simp only [piS, lift_unitary anti d S hh, liftK]
  have hκ : ((Unitary.toUnits κ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (κ : Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [hκ]
  have hsum : ∑ T, (mm anti (κ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) U T *
      (h (Unitary.toUnits κ) * (mm anti (star (κ : Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Sub n k) (Sub n k) ℂ) T S) =
      h (Unitary.toUnits κ) * (mm anti ((κ : Matrix (Fin n) (Fin n) ℂ) *
        star (κ : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Sub n k) (Sub n k) ℂ) U S := by
    rw [mm_mul, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T _ => by ring)
  rw [hsum, unitary_mul_star, mm_one, Matrix.one_apply]
  split_ifs <;> simp

/-- The components of a lift on `GL_n(ℂ)`: the component at `S` is `h`, and the components at
`U ≠ S` with `wt S ≤ wt U` vanish. -/
theorem piS_lift (anti : Bool) (d : Fin n → ComplexCharacterData) (S : Sub n k)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (U : Sub n k) (hU : wt S ≤ wt U) (g : Langlands.GeneralLinear n ℂ) :
    piS anti (lift anti d S h) U g = if U = S then h g else 0 := by
  obtain ⟨a, u, κ, hκ, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [toUnits_of_mem hκ, piS_borel anti (fun T => (lift_mem anti d S hh T).1)]
  simp only [piS_lift_unitary anti d S hh, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  split_ifs with hUS
  · subst hUS
    rw [mm_borel_self, hh.1.2 a u, principalSeriesCharacter_shift]
    ring
  · rw [mm_borel_eq_zero anti a u hU hUS, zero_mul, mul_zero]

/-! ## Decomposition of tuples into lifts -/

theorem mm_diagUnits (anti : Bool) (a : Fin n → ℂˣ) (S U : Sub n k) :
    (mm anti (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      ((1 : upperUnipotent n ℂ) : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S U =
      if S = U then ∏ r ∈ (S : Finset (Fin n)), fac anti (a r) else 0 := by
  have hb : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      ((1 : upperUnipotent n ℂ) : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (a i : ℂ)) := by
    rw [Units.val_mul, Iwasawa.diagonalUnits_val]
    simp
  have hphi : phi anti (Matrix.diagonal (fun i => (a i : ℂ))) =
      Matrix.diagonal (fun i => fac anti (a i)) := by
    cases anti
    · simp [phi, fac]
    · ext i j
      by_cases hij : i = j <;> simp [phi, fac, hij]
  rw [mm, hb, hphi, minorMat_diagonal]

theorem continuous_piS (anti : Bool) {F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ}
    (hF : ∀ T, Continuous (F T)) (S : Sub n k) : Continuous (piS anti F S) :=
  continuous_finsetSum _ (fun T _ => (contMDiff_mm anti S T).continuous.mul (hF T))

open ComplexJacquetNonvanishing in
theorem isTF_piS (anti : Bool) {d : Fin n → ComplexCharacterData}
    {F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ} (hF : ∀ T, F T ∈ KX d) (S : Sub n k) :
    IsTranslateFinite (fun κ : Matrix.unitaryGroup (Fin n) ℂ =>
      piS anti F S (Unitary.toUnits κ)) :=
  isTF_sum _ _ (fun T _ => isTranslateFinite_mul (isTF_mm anti S T) (isTF_restrict (hF T)))

/-- The component `π_S F` on `U(n)` is the restriction of a function of `X(d + e_S)`. -/
theorem exists_component (anti : Bool) (d : Fin n → ComplexCharacterData)
    {F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ} (hF : ∀ T, F T ∈ KX d) (S : Sub n k) :
    ∃ h ∈ KX (shiftChar anti d (S : Finset (Fin n))),
      ∀ κ, h (Unitary.toUnits κ) = piS anti F S (Unitary.toUnits κ) := by
  refine complexPrincipalSeriesExtension n _ (fun κ => piS anti F S (Unitary.toUnits κ)) ?_
    (isTF_piS anti hF S) (fun a κ => ?_)
  · exact (continuous_piS anti (fun T => (hF T).1.1.continuous) S).comp continuous_unitary_toUnits
  · show piS anti F S (Unitary.toUnits (phaseMatrix a * κ)) = _
    rw [ComplexPartialJacquet.phaseMatrix_toUnits, piS_borel anti (fun T => (hF T).1)]
    simp only [mm_diagUnits, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [principalSeriesCharacter_shift]
    ring

/-- Every tuple is the sum of the lifts of its components. -/
theorem eq_sum_lift (anti : Bool) (d : Fin n → ComplexCharacterData)
    {F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ} (hF : ∀ T, F T ∈ KX d)
    (h : Sub n k → Langlands.GeneralLinear n ℂ → ℂ)
    (hh : ∀ S : Sub n k, h S ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (hhF : ∀ (S : Sub n k) κ, h S (Unitary.toUnits κ) = piS anti F S (Unitary.toUnits κ))
    (T : Sub n k) :
    F T = ∑ S, lift anti d S (h S) T := by
  refine eq_of_eq_unitary (hF T).1
    (Submodule.sum_mem _ (fun S _ => (lift_mem anti d S (hh S) T).1)) (fun κ => ?_)
  rw [Finset.sum_apply]
  simp only [lift_unitary anti d _ (hh _), liftK, hhF, piS]
  have hκ : ((Unitary.toUnits κ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      (κ : Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [hκ]
  have h1 : ∑ S, (∑ T', (mm anti (κ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ)
      S T' * F T' (Unitary.toUnits κ)) *
        (mm anti (star (κ : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Sub n k) (Sub n k) ℂ) T S =
      ∑ T', (mm anti (star (κ : Matrix (Fin n) (Fin n) ℂ) * (κ : Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Sub n k) (Sub n k) ℂ) T T' * F T' (Unitary.toUnits κ) := by
    simp only [mm_mul, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun T' _ => Finset.sum_congr rfl (fun S _ => by ring))
  rw [h1, star_mul_unitary, mm_one]
  simp [Matrix.one_apply]

/-! ## The Lie algebra action on tuples -/

/-- The action of a real direction `X` on tuples: `(X·F)_T = R(X) F_T + ∑_{T'} D_{T T'}(X) F_{T'}`,
the action on `X(d) ⊗ Λ^k`. -/
def act (anti : Bool) (X : Matrix (Fin n) (Fin n) ℂ) (F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ)
    (T : Sub n k) : Langlands.GeneralLinear n ℂ → ℂ :=
  fun g => rightDerivative (matrixModel ℂ n) X (F T) g + ∑ T', Dco anti T T' X * F T' g

theorem act_eq (anti : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ) (T : Sub n k) :
    act anti X F T = rightDerivative (matrixModel ℂ n) X (F T) + ∑ T', Dco anti T T' X • F T' := by
  funext g
  simp [act, Finset.sum_apply]

theorem act_mem (anti : Bool) {d : Fin n → ComplexCharacterData} (X : Matrix (Fin n) (Fin n) ℂ)
    {F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ} (hF : ∀ T, F T ∈ KX d) (T : Sub n k) :
    act anti X F T ∈ KX d := by
  rw [act_eq]
  exact Submodule.add_mem _ (rightDerivative_mem_kFiniteFunctions_principalSeries _ _ (hF T) X)
    (Submodule.sum_mem _ (fun T' _ => Submodule.smul_mem _ _ (hF T')))

theorem rightDerivative_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Langlands.GeneralLinear n ℂ → ℂ)
    (hf : ∀ i, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (f i)) (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X (∑ i ∈ s, f i) =
      ∑ i ∈ s, rightDerivative (matrixModel ℂ n) X (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ComplexStrictLanglandsQuotient.rightDerivative_zero (n := n) X
  | insert i s hi ih =>
    have hs : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (∑ j ∈ s, f j) := by
      have : (∑ j ∈ s, f j) = fun g => ∑ j ∈ s, f j g := by
        funext g; simp [Finset.sum_apply]
      rw [this]
      exact contMDiff_finsetSum (fun j _ => hf j)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, rightDerivative_add (hf i) hs X, ih]

/-- The components intertwine the action on tuples with right derivatives. -/
theorem piS_act (anti : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    {F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ}
    (hF : ∀ T, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (F T)) (S : Sub n k)
    (g : Langlands.GeneralLinear n ℂ) :
    piS anti (act anti X F) S g = rightDerivative (matrixModel ℂ n) X (piS anti F S) g := by
  have hpi : piS anti F S = ∑ T, fun g : Langlands.GeneralLinear n ℂ =>
      (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S T * F T g := by
    funext g; simp [piS, Finset.sum_apply]
  rw [hpi, rightDerivative_finset_sum _ _
      (fun T => ComplexJacquetLimit.contMDiff_mul_fun (contMDiff_mm anti S T) (hF T)),
    Finset.sum_apply]
  have h1 : ∀ T, rightDerivative (matrixModel ℂ n) X (fun g : Langlands.GeneralLinear n ℂ =>
      (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S T * F T g) g =
      (∑ U, (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S U *
        Dco anti U T X) * F T g +
      (mm anti (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n k) (Sub n k) ℂ) S T *
        rightDerivative (matrixModel ℂ n) X (F T) g := by
    intro T
    rw [ComplexTemperedComplement.rightDerivative_mul_fun (contMDiff_mm anti S T) (hF T),
      rightDerivative_mm]
  simp only [h1, piS, act, mul_add, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

end Langlands.Archimedean.JacquetTranslation
