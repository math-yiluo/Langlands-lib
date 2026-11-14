import Langlands.Automorphic.CuspidalWhittaker.CurveDerivative
import Langlands.Automorphic.CuspidalWhittaker.MixedTraceFormula
import Langlands.Automorphic.CuspidalUnitaryForm

/-!
# Whittaker functionals at the archimedean places of a cuspidal realization

Let `S` be a cuspidal actual operator realization of `GL_{r+1}` over a number field `F`.
For `h ∈ GL_{r+1}(𝔸_F)` the map `ℓ_h : x ↦ W_x(h)`, the iterated Whittaker coefficient of the
realized form of `x` evaluated at `h`, is a linear form on `S`. This module shows how `ℓ_h`
transforms under a real Lie direction `Y` whose matrix `M` in mixed coordinates squares to
zero: if `N = A M A⁻¹`, with `A` the archimedean component of `h` in mixed coordinates, is
strictly upper triangular, then

`ℓ_h (Y · x) = 2π i · Tr(∑ᵢ N_{i,i+1}) · ℓ_h x`,

where `Tr` is the trace of the mixed space `ℝ^{r₁} × ℂ^{r₂}`. The proof differentiates
`s ↦ W_x(h · exp(s Y))` at `s = 0`: on one side by the Lie action, on the other by the
equivariance of `W_x` under the upper unitriangular matrices `h exp(s Y) h⁻¹ = 1 + s N`.
-/

noncomputable section

universe u

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global Langlands.Automorphic.ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F]

/-! ### Square-zero exponentials and conjugation -/

omit [NumberField F] in
/-- The exponential of a square-zero direction is affine: `exp (s M) = 1 + s M`. -/
theorem exp_smul_of_mul_self_eq_zero {n : ℕ} {M : ArchimedeanMatrix F n} (hM : M * M = 0)
    (s : ℝ) : NormedSpace.exp (s • M) = 1 + s • M := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [smul_pow, pow_add (M), sq, hM, zero_mul, smul_zero, smul_zero]

/-- Conjugating an infinite element by an adelic element only sees its infinite component. -/
theorem mul_ofInfinite_mul_inv {n : ℕ} (h : AdelicGL F n) (c : InfiniteAdelicGL F n) :
    h * AdelicGL.ofInfinite F n c * h⁻¹ =
      AdelicGL.ofInfinite F n (AdelicGL.infinite F n h * c * (AdelicGL.infinite F n h)⁻¹) := by
  apply AdelicGL.ext_infinite_finite F n
  · rw [map_mul, map_mul, map_inv, AdelicGL.infinite_ofInfinite, AdelicGL.infinite_ofInfinite]
  · rw [map_mul, map_mul, map_inv, AdelicGL.finite_ofInfinite, AdelicGL.finite_ofInfinite,
      mul_one, mul_inv_cancel]

theorem ofInfinite_val_apply {n : ℕ} (g : InfiniteAdelicGL F n) (i j : Fin n) :
    (AdelicGL.ofInfinite F n g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
      ((g : Matrix (Fin n) (Fin n) (InfiniteAdeles F)) i j,
        (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) i j) := by
  apply Prod.ext
  · change AdelicGL.infinite F n (AdelicGL.ofInfinite F n g) i j = _
    rw [AdelicGL.infinite_ofInfinite]
  · change AdelicGL.finite F n (AdelicGL.ofInfinite F n g) i j = _
    rw [AdelicGL.finite_ofInfinite]
    rfl

/-- In mixed coordinates, conjugating the one-parameter subgroup of a square-zero direction
`M` by `A` gives `1 + s A M A⁻¹`. -/
theorem coordinates_conj_oneParameter {n : ℕ} (a : InfiniteAdelicGL F n)
    (Y : ArchimedeanGL.RealLieAlgebra F n)
    (hY : ArchimedeanGL.realLieAlgebraToMatrix F n Y *
      ArchimedeanGL.realLieAlgebraToMatrix F n Y = 0) (s : ℝ) :
    ((archimedeanGLCoordinates F n
        (a * ArchimedeanGL.infiniteOneParameter F n Y s * a⁻¹) : ArchimedeanGL F n) :
        ArchimedeanMatrix F n) =
      1 + s • ((archimedeanGLCoordinates F n a : ArchimedeanMatrix F n) *
        ArchimedeanGL.realLieAlgebraToMatrix F n Y *
          ((archimedeanGLCoordinates F n a)⁻¹ : ArchimedeanGL F n)) := by
  rw [map_mul, map_mul, map_inv, ArchimedeanGL.infiniteOneParameter,
    ContinuousMulEquiv.apply_symm_apply, Units.val_mul, Units.val_mul,
    ArchimedeanGL.oneParameter_val, exp_smul_of_mul_self_eq_zero hY, mul_add, add_mul, mul_one,
    Units.mul_inv, mul_smul_comm, smul_mul_assoc, mul_assoc]

/-- The direction `A M A⁻¹`, where `A` is the archimedean component of `h` in mixed
coordinates and `M` is the matrix of `Y`. -/
def conjDirection {n : ℕ} (h : AdelicGL F n) (Y : ArchimedeanGL.RealLieAlgebra F n) :
    ArchimedeanMatrix F n :=
  (archimedeanGLCoordinates F n (AdelicGL.infinite F n h) : ArchimedeanMatrix F n) *
    ArchimedeanGL.realLieAlgebraToMatrix F n Y *
      ((archimedeanGLCoordinates F n (AdelicGL.infinite F n h))⁻¹ : ArchimedeanGL F n)

/-! ### Upper unitriangular infinite elements -/

section Unipotent

variable {r : ℕ}

theorem superSum_ofInfinite (c : InfiniteAdelicGL F (r + 1)) :
    superSum 0 (AdelicGL.ofInfinite F (r + 1) c) =
      ((∑ i : Fin r,
        (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (NumberField.InfiniteAdeleRing F)) i.castSucc i.succ,
        0) : Adeles F) := by
  unfold superSum
  apply adeles_ext
  · rw [Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ite_eq_left (Nat.zero_le _), ofInfinite_val_apply]
  · rw [Prod.snd_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_left (Nat.zero_le _), ofInfinite_val_apply, Matrix.one_apply_ne]
    exact ne_of_lt (Fin.castSucc_lt_succ (i := i))

theorem isUpperColId_ofInfinite {c : InfiniteAdelicGL F (r + 1)}
    (hc : ∀ i j : Fin (r + 1), (j : ℕ) ≤ i →
      (archimedeanGLCoordinates F (r + 1) c : ArchimedeanMatrix F (r + 1)) i j =
        (1 : ArchimedeanMatrix F (r + 1)) i j) :
    IsUpperColId 0 (AdelicGL.ofInfinite F (r + 1) c).val := by
  intro i j hij
  have hji : (j : ℕ) ≤ i := by
    rcases hij with h | h
    · exact h
    · omega
  have h1 : (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (NumberField.InfiniteAdeleRing F)) i j =
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (NumberField.InfiniteAdeleRing F)) i j := by
    apply (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    change (archimedeanGLCoordinates F (r + 1) c : ArchimedeanMatrix F (r + 1)) i j = _
    rw [hc i j hji, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    exacts [(map_one _).symm, (map_zero _).symm]
  rw [ofInfinite_val_apply, h1, Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

/-- The infinite trace of the superdiagonal of `A exp(s Y) A⁻¹`, for a square-zero `Y`. -/
theorem infiniteTrace_superdiagonal_conj (h : AdelicGL F (r + 1))
    (Y : ArchimedeanGL.RealLieAlgebra F (r + 1))
    (hY : ArchimedeanGL.realLieAlgebraToMatrix F (r + 1) Y *
      ArchimedeanGL.realLieAlgebraToMatrix F (r + 1) Y = 0) (s : ℝ) :
    infiniteTrace F (∑ i : Fin r,
      ((AdelicGL.infinite F (r + 1) h * ArchimedeanGL.infiniteOneParameter F (r + 1) Y s *
        (AdelicGL.infinite F (r + 1) h)⁻¹ : InfiniteAdelicGL F (r + 1)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (NumberField.InfiniteAdeleRing F)) i.castSucc i.succ) =
      s * mixedTrace F (∑ i : Fin r, conjDirection h Y i.castSucc i.succ) := by
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [infiniteTrace_apply]
  change mixedTrace F ((archimedeanGLCoordinates F (r + 1)
    (AdelicGL.infinite F (r + 1) h * ArchimedeanGL.infiniteOneParameter F (r + 1) Y s *
      (AdelicGL.infinite F (r + 1) h)⁻¹) : ArchimedeanMatrix F (r + 1)) i.castSucc i.succ) = _
  rw [coordinates_conj_oneParameter _ Y hY s, Matrix.add_apply,
    Matrix.one_apply_ne (ne_of_lt (Fin.castSucc_lt_succ (i := i))), zero_add, Matrix.smul_apply,
    map_smul, smul_eq_mul]
  rfl

/-! ### Derivatives of Whittaker coefficients along square-zero directions -/

/-- **Function-level form of the Lie derivative formula.** Let `e(s) = exp(s Y)` (as an
infinite adelic element) for a direction `Y` with square-zero matrix such that
`N = A M A⁻¹` is strictly upper triangular. If `Ψ` is the derivative of `Φ` along right
translation by `e` and both have the level-`r` properties, then
`W_Ψ(h) = 2π i · Tr(∑ᵢ N_{i,i+1}) · W_Φ(h)`. -/
theorem descend_eq_of_hasCurveDeriv [CompactSpace (AdeleQuotient F)]
    {Φ Ψ : AdelicGL F (r + 1) → ℂ} (hΦ : LevelProps r Φ) (hΨ : LevelProps r Ψ)
    (h : AdelicGL F (r + 1)) (Y : ArchimedeanGL.RealLieAlgebra F (r + 1))
    (hY : ArchimedeanGL.realLieAlgebraToMatrix F (r + 1) Y *
      ArchimedeanGL.realLieAlgebraToMatrix F (r + 1) Y = 0)
    (hN : ∀ i j : Fin (r + 1), (j : ℕ) ≤ i → conjDirection h Y i j = 0)
    (e : ℝ → AdelicGL F (r + 1))
    (he_val : ∀ s, e s =
      AdelicGL.ofInfinite F (r + 1) (ArchimedeanGL.infiniteOneParameter F (r + 1) Y s))
    (hd : HasCurveDeriv e Φ Ψ) :
    descend r Ψ h =
      (((2 * Real.pi * mixedTrace F (∑ i : Fin r, conjDirection h Y i.castSucc i.succ) : ℝ) :
        ℂ) * Complex.I) * descend r Φ h := by
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ,
      mixedTrace F (∑ i : Fin r, conjDirection h Y i.castSucc i.succ) = τ := ⟨_, rfl⟩
  rw [hτ]
  have he : Continuous e := by
    rw [show e = fun s => AdelicGL.ofInfinite F (r + 1)
        (ArchimedeanGL.infiniteOneParameter F (r + 1) Y s) from funext he_val]
    exact (map_continuous (AdelicGL.ofInfinite F (r + 1))).comp
      (ArchimedeanGL.continuous_infiniteOneParameter F (r + 1) Y)
  have hD : HasDerivAt (fun s => descend r Φ (h * e s)) (descend r Ψ h) 0 := by
    have h0 := HasCurveDeriv.descend he r le_rfl Φ Ψ hΦ hΨ hd h 0
    have hh : h * e 0 = h := by
      rw [he_val, ArchimedeanGL.infiniteOneParameter_zero, map_one, mul_one]
    rw [hh] at h0
    exact h0
  have hL := levelProps_descend r le_rfl Φ hΦ
  have hchar : ∀ a : NumberField.InfiniteAdeleRing F,
      adelicCharacter F ((a, 0) : Adeles F) = unitExp (infiniteTrace F a) := fun a =>
    adelicCharacter_of_integral F (a, 0) (zero_mem _)
  have hfun : ∀ s : ℝ, descend r Φ (h * e s) =
      Complex.exp (((2 * Real.pi * (s * τ) : ℝ) : ℂ) * Complex.I) * descend r Φ h := by
    intro s
    have hconj : h * e s * h⁻¹ = AdelicGL.ofInfinite F (r + 1)
        (AdelicGL.infinite F (r + 1) h * ArchimedeanGL.infiniteOneParameter F (r + 1) Y s *
          (AdelicGL.infinite F (r + 1) h)⁻¹) := by
      rw [he_val]
      exact mul_ofInfinite_mul_inv h _
    have hup : IsUpperColId 0 (h * e s * h⁻¹).val := by
      rw [hconj]
      refine isUpperColId_ofInfinite fun i j hji => ?_
      rw [coordinates_conj_oneParameter _ Y hY s, Matrix.add_apply, Matrix.smul_apply]
      have hz : conjDirection h Y i j = 0 := hN i j hji
      unfold conjDirection at hz
      rw [hz, smul_zero, add_zero]
    have hmul : h * e s = h * e s * h⁻¹ * h := (inv_mul_cancel_right (h * e s) h).symm
    rw [hmul, hL.equivariant _ h hup, hconj, superSum_ofInfinite, hchar,
      infiniteTrace_superdiagonal_conj h Y hY s, hτ, unitExp, Circle.coe_exp]
  have hD2 : HasDerivAt
      (fun s : ℝ => Complex.exp (((2 * Real.pi * (s * τ) : ℝ) : ℂ) * Complex.I) * descend r Φ h)
      ((((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I) * descend r Φ h) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * Real.pi * (s * τ)) (2 * Real.pi * (1 * τ)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const τ).const_mul (2 * Real.pi)
    have h2 := ((h1.ofReal_comp.mul_const Complex.I).cexp).mul_const (descend r Φ h)
    convert h2 using 1
    simp
  exact (hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (hfun s).symm)).unique hD2

end Unipotent

/-! ### The functional `x ↦ W_x(h)` on a cuspidal operator realization -/

section Realization

local instance archFunctionalRationalAddCommGroup {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance archFunctionalContinuousAddCommGroup {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance archFunctionalSmoothAddCommGroup {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance archFunctionalFormsAddCommGroup {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance archFunctionalStableAddCommGroup {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance archFunctionalSpaceAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (S : OperatorRealization F (r + 1))

theorem levelProps_realization (hS : S.IsCuspidal) (x : S.Space) :
    LevelProps r (evaluate F (r + 1) (S.toContinuous x)) :=
  levelProps_top _ fun _ _ h ha hb g => S.constantTerm_eq_zero hS h ha hb x g

/-- The linear form `x ↦ W_x(h)` on a cuspidal operator realization. -/
def realizationFunctional (hS : S.IsCuspidal) (h : AdelicGL F (r + 1)) :
    Module.Dual ℂ S.Space where
  toFun x := descend r (evaluate F (r + 1) (S.toContinuous x)) h
  map_add' x y := by
    rw [show evaluate F (r + 1) (S.toContinuous (x + y)) = fun a =>
        evaluate F (r + 1) (S.toContinuous x) a + evaluate F (r + 1) (S.toContinuous y) a from
      funext fun a => congrArg (fun f => evaluate F (r + 1) f a) (map_add S.toContinuous x y)]
    exact descend_add r le_rfl _ _ (levelProps_realization S hS x)
      (levelProps_realization S hS y) h
  map_smul' c x := by
    rw [show evaluate F (r + 1) (S.toContinuous (c • x)) = fun a =>
        c * evaluate F (r + 1) (S.toContinuous x) a from
      funext fun a => congrArg (fun f => evaluate F (r + 1) f a) (map_smul S.toContinuous c x)]
    exact descend_const_mul r c _ h

theorem realizationFunctional_apply (hS : S.IsCuspidal) (h : AdelicGL F (r + 1))
    (x : S.Space) :
    realizationFunctional S hS h x = descend r (evaluate F (r + 1) (S.toContinuous x)) h :=
  rfl

/-- **Lie derivatives of the functional.** If `Y` has square-zero matrix `M` and
`N = A M A⁻¹` is strictly upper triangular, where `A` is the archimedean component of `h`,
then `ℓ_h (Y · x) = 2π i · Tr(∑ᵢ N_{i,i+1}) · ℓ_h x`. -/
theorem realizationFunctional_lieOperator (hS : S.IsCuspidal) (h : AdelicGL F (r + 1))
    (Y : ArchimedeanGL.RealLieAlgebra F (r + 1))
    (hY : ArchimedeanGL.realLieAlgebraToMatrix F (r + 1) Y *
      ArchimedeanGL.realLieAlgebraToMatrix F (r + 1) Y = 0)
    (hN : ∀ i j : Fin (r + 1), (j : ℕ) ≤ i → conjDirection h Y i j = 0) (x : S.Space) :
    realizationFunctional S hS h (S.lieOperator Y x) =
      (((2 * Real.pi * mixedTrace F (∑ i : Fin r, conjDirection h Y i.castSucc i.succ) : ℝ) :
        ℂ) * Complex.I) * realizationFunctional S hS h x :=
  descend_eq_of_hasCurveDeriv (levelProps_realization S hS x)
    (levelProps_realization S hS (S.lieOperator Y x)) h Y hY hN
    (fun s => AdelicGL.ofInfinite F (r + 1) (ArchimedeanGL.infiniteOneParameter F (r + 1) Y s))
    (fun _ => rfl) (fun g t => S.hasDerivAt_evaluate_oneParameter Y x g t)

end Realization

end Langlands.Automorphic.CuspidalWhittaker
