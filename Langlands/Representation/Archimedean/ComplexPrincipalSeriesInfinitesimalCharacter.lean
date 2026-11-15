import Langlands.Representation.Archimedean.JacquetFunctionalCenter
import Langlands.Representation.Archimedean.ComplexGenericLargeReduction
import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Langlands.Representation.Archimedean.ComplexDuality.GramWeight
import Langlands.Representation.Archimedean.Kostant.Transport

/-!
# Complex principal series have an infinitesimal character

`ComplexPrincipalSeriesInfinitesimalCharacterStatement`: for every `n` and all characters
`χ`, the action `principalSeriesLie ℂ n χ` of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` on the `U(n)`-finite functions of
the principal series of `GL_n(ℂ)` has an infinitesimal character: every central element of
the enveloping algebra acts by a scalar. In particular so does every complex standard module
(`complexStandardLie_hasInfinitesimalCharacter`).
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Complex principal series have an infinitesimal character.** For all `n` and all
characters `χ`, every central element of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` acts by a scalar on the
`U(n)`-finite functions of the principal series `principalSeries ℂ n χ`. -/
def ComplexPrincipalSeriesInfinitesimalCharacterStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℂˣ → ℂ), HasInfinitesimalCharacter (principalSeriesLie ℂ n χ)

namespace ComplexPrincipalSeriesInfChar

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean InfinitesimalCharacter
open ComplexGenericLarge ComplexDuality ComplexDuality.LieInvariance JacquetCenter

variable {n : ℕ}

/-! ## Upper triangular derivatives at the identity -/

/-- A function vanishing on the invertible diagonal matrices has zero derivative at `1` along
every diagonal matrix. -/
theorem fderiv_diagonal_eq_zero {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hΦd : DifferentiableAt ℝ Φ 1)
    (hΦ : ∀ a : Fin n → ℂˣ, Φ (Matrix.diagonal fun i => (a i : ℂ)) = 0) (d : Fin n → ℂ) :
    fderiv ℝ Φ 1 (Matrix.diagonal d) = 0 := by
  let a : ℝ → Fin n → ℂˣ := fun t i => Units.mk0 (Complex.exp ((t : ℂ) * d i))
    (Complex.exp_ne_zero _)
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • Matrix.diagonal d) =
      Matrix.diagonal fun i => (a t i : ℂ) := fun t => by
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    simp [a, Complex.real_smul]
  have hγ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Matrix.diagonal d))
      (Matrix.diagonal d) 0 := by
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.diagonal d) 0
    simpa using h
  have hcomp := hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hfun : (Φ ∘ fun t : ℝ => NormedSpace.exp (t • Matrix.diagonal d)) = fun _ => 0 := by
    funext t
    simp only [Function.comp_apply, hexp, hΦ]
  rw [hfun] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 _)

/-- For `f` in the principal series of `GL_n(ℂ)` with `f(1) = 0` and `X` upper triangular,
`(R(X) f)(1) = 0`: `f` vanishes on the invertible upper triangular matrices. -/
theorem rightDerivative_apply_one_eq_zero {χ : ℕ → ℂˣ → ℂ}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ) (h1 : f 1 = 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i j, j < i → X i j = 0) :
    rightDerivative (matrixModel ℂ n) X f 1 = 0 := by
  rw [rightDerivative_eq_fderiv hf.1, Units.val_one, one_mul]
  have hd : DifferentiableAt ℝ (unitsExtension f) 1 := by
    have h := (contDiffAt_unitsExtension hf.1 (1 : Langlands.GeneralLinear n ℂ)).differentiableAt
      (by simp)
    rwa [Units.val_one] at h
  have hval : unitsExtension f 1 = f 1 := by
    simpa using unitsExtension_val f (1 : Langlands.GeneralLinear n ℂ)
  have hsplit : X = Matrix.diagonal (fun i => X i i) + (X - Matrix.diagonal fun i => X i i) := by
    abel
  have hN : ∀ i j, j ≤ i → (X - Matrix.diagonal fun i => X i i) i j = 0 := by
    intro i j hji
    rcases hji.lt_or_eq with h | rfl
    · rw [Matrix.sub_apply, hX i j h, Matrix.diagonal_apply_ne _ h.ne', sub_zero]
    · rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self]
  have hu : ∀ u : upperUnipotent n ℂ,
      unitsExtension f (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * 1) =
        unitsExtension f 1 := by
    intro u
    have h := unitsExtension_unipotent_mul hf u 1
    rw [Units.val_one] at h
    rw [h, h1, mul_zero, hval, h1]
  have h2 := fderiv_strictUpper_mul_eq_zero hd hu hN
  rw [mul_one] at h2
  rw [hsplit, map_add, h2, add_zero]
  refine fderiv_diagonal_eq_zero hd (fun a => ?_) _
  have h := unitsExtension_diagonal_mul hf a 1
  rwa [Units.val_one, mul_one, h1, mul_zero] at h

/-- A linear functional vanishing on the kernel of `ψ` is a multiple of `ψ`. -/
theorem exists_eq_smul_of_ker_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    {φ ψ : V →ₗ[ℂ] ℂ} (h : ∀ v, ψ v = 0 → φ v = 0) : ∃ c : ℂ, φ = c • ψ := by
  by_cases hψ : ψ = 0
  · refine ⟨0, LinearMap.ext fun v => ?_⟩
    rw [h v (by rw [hψ, LinearMap.zero_apply]), zero_smul, LinearMap.zero_apply]
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀, ψ v₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hψ (LinearMap.ext hc)
    refine ⟨φ v₀ / ψ v₀, LinearMap.ext fun v => ?_⟩
    have hk : ψ (v - (ψ v / ψ v₀) • v₀) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀, sub_self]
    have h' := h _ hk
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h'
    rw [LinearMap.smul_apply, smul_eq_mul, h']
    ring

/-! ## Evaluation at the identity -/

variable (χ : ℕ → ℂˣ → ℂ)

/-- Evaluation at `1` on the `U(n)`-finite functions of the principal series. -/
abbrev evalOne : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →ₗ[ℂ] ℂ :=
  kFiniteEval (principalSeries ℂ n χ) 1

/-- `1 ⊗ X` acts on evaluation at `1` by a scalar for every upper triangular `X`. -/
theorem one_tmul_mem_scalarSubmodule {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, j < i → X i j = 0) :
    ((1 : ℂ) ⊗ₜ[ℝ] X) ∈ scalarSubmodule (principalSeriesLie ℂ n χ) (evalOne χ) := by
  rw [mem_scalarSubmodule]
  refine exists_eq_smul_of_ker_le fun f hf => ?_
  rw [LinearMap.comp_apply, kFiniteEval_apply, principalSeriesLie_one_tmul_apply_coe]
  rw [kFiniteEval_apply] at hf
  exact rightDerivative_apply_one_eq_zero f.2.1 hf hX

/-- An element `Y = (Y₀, Y₁)` of `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` with both components upper triangular acts
on evaluation at `1` by a scalar. -/
theorem mem_scalarSubmodule_prod {Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ}
    (hY : ∀ r, ∀ i j, j < i → Y r i j = 0) :
    Y ∈ scalarSubmodule (prodAction (principalSeriesLie ℂ n χ)) (evalOne χ) := by
  have hS : tensorInv Y ∈ scalarSubmodule (principalSeriesLie ℂ n χ) (evalOne χ) := by
    have h0 : ∀ i j, j < i → (Complex.I • Y 0) i j = 0 := fun i j h => by
      rw [Matrix.smul_apply, hY 0 i j h, smul_zero]
    have h1 : ∀ i j, j < i → conjMat (Y 1) i j = 0 := fun i j h => by
      rw [conjMat_apply, hY 1 i j h, map_zero]
    have h1' : ∀ i j, j < i → (Complex.I • conjMat (Y 1)) i j = 0 := fun i j h => by
      rw [Matrix.smul_apply, h1 i j h, smul_zero]
    rw [tensorInv]
    refine Submodule.smul_mem _ _ (add_mem (add_mem (sub_mem ?_ ?_) ?_) ?_)
    · exact one_tmul_mem_scalarSubmodule χ (hY 0)
    · exact Submodule.smul_mem _ _ (one_tmul_mem_scalarSubmodule χ h0)
    · exact one_tmul_mem_scalarSubmodule χ h1
    · exact Submodule.smul_mem _ _ (one_tmul_mem_scalarSubmodule χ h1')
  obtain ⟨c, hc⟩ := hS
  exact ⟨c, by rw [prodAction_apply, tensorEquiv_symm_apply, hc]⟩

/-! ## The lowering elements -/

/-- The weight element `H = (D, D)`, `D = diag(0, -1, …, -(n-1))`. -/
def weightH : Fin 2 → Matrix (Fin n) (Fin n) ℂ :=
  fun _ => Matrix.diagonal fun p => -((p : ℕ) : ℂ)

/-- The lowering elements: `(E, 0)` and `(0, E)` for `E` a multiple of a strictly lower
triangular matrix unit. -/
def lowering : Set (Fin 2 → Matrix (Fin n) (Fin n) ℂ) :=
  {y | ∃ (r : Fin 2) (p q : Fin n) (a : ℂ), q < p ∧ y = Pi.single r (Matrix.single p q a)}

theorem diagonal_mul_sub_mul_diagonal (d : Fin n → ℂ) (p q : Fin n) (a : ℂ) :
    Matrix.diagonal d * Matrix.single p q a - Matrix.single p q a * Matrix.diagonal d =
      (d p - d q) • Matrix.single p q a := by
  ext r s
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · ring

theorem lie_weightH_lowering :
    ∀ y ∈ (lowering : Set (Fin 2 → Matrix (Fin n) (Fin n) ℂ)),
      ∃ k : ℕ, 0 < k ∧ ⁅(weightH : Fin 2 → Matrix (Fin n) (Fin n) ℂ), y⁆ = -((k : ℂ) • y) := by
  rintro y ⟨r, p, q, a, hqp, rfl⟩
  refine ⟨(p : ℕ) - (q : ℕ), Nat.sub_pos_of_lt hqp, ?_⟩
  rw [Ring.lie_def]
  funext s
  rw [Pi.sub_apply, Pi.mul_apply, Pi.mul_apply, Pi.neg_apply, Pi.smul_apply]
  by_cases hs : s = r
  · subst hs
    rw [Pi.single_eq_same, weightH, diagonal_mul_sub_mul_diagonal,
      Nat.cast_sub (Fin.le_iff_val_le_val.1 hqp.le), ← neg_smul]
    congr 1
    ring
  · rw [Pi.single_eq_of_ne hs, mul_zero, zero_mul, sub_zero, smul_zero, neg_zero]

/-- Every element of `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` acts on evaluation at `1` by a scalar plus an element
of the span of the lowering elements. -/
theorem decSubmodule_eq_top :
    decSubmodule (prodAction (principalSeriesLie ℂ n χ)) (evalOne χ) lowering = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = ∑ r : Fin 2, ∑ p : Fin n, ∑ q : Fin n, Pi.single r (Matrix.single p q (x r p q)) := by
    funext r
    conv_lhs => rw [Matrix.matrix_eq_sum_single (x r)]
    fin_cases r <;> simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  refine Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun p _ =>
    Submodule.sum_mem _ fun q _ => ?_
  rcases lt_or_ge q p with hqp | hpq
  · exact subset_decSubmodule _ _ _ ⟨r, p, q, _, hqp, rfl⟩
  · refine scalarSubmodule_le_decSubmodule _ _ _ (mem_scalarSubmodule_prod χ fun s i j hji => ?_)
    by_cases hs : s = r
    · subst hs
      rw [Pi.single_eq_same, Matrix.single_apply]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd hpq (not_le.2 hji)
      · rfl
    · rw [Pi.single_eq_of_ne hs, Matrix.zero_apply]

/-! ## The infinitesimal character -/

/-- **Complex principal series have an infinitesimal character.** -/
theorem hasInfinitesimalCharacter_principalSeriesLie :
    HasInfinitesimalCharacter (principalSeriesLie ℂ n χ) := by
  refine Kostant.hasInfinitesimalCharacter_of_comp tensorLieEquiv ?_
  intro z hz
  obtain ⟨μ, hμ⟩ := mem_scalarSubmodule_prod χ
      (Y := (weightH : Fin 2 → Matrix (Fin n) (Fin n) ℂ)) fun r i j h => by
    rw [weightH, Matrix.diagonal_apply_ne _ h.ne']
  have hdec : ∀ x, ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ lowering,
      evalOne χ ∘ₗ prodAction (principalSeriesLie ℂ n χ) x =
        c • evalOne χ + evalOne χ ∘ₗ prodAction (principalSeriesLie ℂ n χ) y := fun x =>
    (mem_decSubmodule _ _ _).1 (by rw [decSubmodule_eq_top χ]; trivial)
  obtain ⟨c, hc⟩ := exists_comp_envelopingAction_eq_smul weightH μ hμ lie_weightH_lowering hdec hz
  refine ⟨c, ?_⟩
  set Z := envelopingAction (prodAction (principalSeriesLie ℂ n χ)) z with hZdef
  have hZρ : ∀ k, principalSeriesRep ℂ n χ k * Z = Z * principalSeriesRep ℂ n χ k := by
    intro k
    rw [hZdef, rho_mul_envelopingAction_prod (isComplexGKModule_principalSeries n χ).2.2.2 k z,
      pairFixesCenter_of_det_ne_zero _ (det_ne_zero_of_unitary k) (pairUnit k) (pairUnit_val k)
        z hz]
  have hev : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ)
      (F : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)),
      evalOne χ (principalSeriesRep ℂ n χ k F) =
        (F : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) := by
    intro k F
    rw [kFiniteEval_apply, principalSeriesRep_apply_coe]
    change (F : Langlands.GeneralLinear n ℂ → ℂ) (1 * Unitary.toUnits k) = _
    rw [one_mul]
  refine LinearMap.ext fun f => ?_
  rw [Module.algebraMap_end_apply]
  apply Subtype.ext
  have hmem : ((Z f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
      Langlands.GeneralLinear n ℂ → ℂ) - c • (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
        principalSeries ℂ n χ :=
    sub_mem (Z f).2.1 (Submodule.smul_mem _ c f.2.1)
  have h0 := eq_zero_of_mem_principalSeries_of_eqOn hmem fun g hg => by
    let k : Matrix.unitaryGroup (Fin n) ℂ :=
      ⟨((g : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), hg⟩
    have hk : (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) = g := Units.ext rfl
    have h1 := hev k (Z f)
    rw [← Module.End.mul_apply, hZρ k, Module.End.mul_apply] at h1
    have h2 := LinearMap.congr_fun hc (principalSeriesRep ℂ n χ k f)
    rw [LinearMap.comp_apply, LinearMap.smul_apply, hev k f, hk] at h2
    rw [hk] at h1
    rw [Pi.sub_apply, Pi.smul_apply, ← h1, h2, sub_self]
  rw [Submodule.coe_smul]
  exact sub_eq_zero.1 h0

end ComplexPrincipalSeriesInfChar

open Langlands.LocalFactor.Archimedean ComplexPrincipalSeriesInfChar in
/-- Proof of `ComplexPrincipalSeriesInfinitesimalCharacterStatement`. -/
theorem complexPrincipalSeriesInfinitesimalCharacter :
    ComplexPrincipalSeriesInfinitesimalCharacterStatement := fun _ χ =>
  hasInfinitesimalCharacter_principalSeriesLie χ

open Langlands.LocalFactor.Archimedean in
/-- Every complex standard module has an infinitesimal character. -/
theorem complexStandardLie_hasInfinitesimalCharacter (n : ℕ) (ds : List ComplexCharacterData) :
    HasInfinitesimalCharacter (complexStandardLie n ds) :=
  complexPrincipalSeriesInfinitesimalCharacter n _

end Langlands.Archimedean
