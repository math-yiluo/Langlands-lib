import Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-!
# Real principal series have an infinitesimal character

`RealPrincipalSeriesInfinitesimalCharacterStatement`: for every `n` and all characters `χ`,
the action `principalSeriesLie ℝ n χ` of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` on the `O(n)`-finite functions of the
principal series of `GL_n(ℝ)` has an infinitesimal character: every central element of the
enveloping algebra acts by a scalar.

The proof (`hasInfinitesimalCharacter_kFiniteLie`) applies to the `O(n)`-finite functions of
every space `V` of principal-series functions stable under right translation by `O(n)` and
under right derivatives. In particular every real standard module has an infinitesimal
character (`realStandardLie_hasInfinitesimalCharacter`).
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Real principal series have an infinitesimal character.** For all `n` and all
characters `χ`, every central element of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))` acts by a scalar on the
`O(n)`-finite functions of the principal series `principalSeries ℝ n χ`. -/
def RealPrincipalSeriesInfinitesimalCharacterStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℝˣ → ℂ), HasInfinitesimalCharacter (principalSeriesLie ℝ n χ)

namespace RealPrincipalSeriesInfChar

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean InfinitesimalCharacter
open JacquetCenter RealPrincipalSeriesDuality

variable {n : ℕ}

/-! ## Upper triangular derivatives -/

/-- A principal-series function vanishing at `g` has zero derivative at `g` along `U g` for
every upper triangular `U`: it vanishes on the curve `exp(t diag U) (1 + t N) g`, `N` the
strictly upper triangular part of `U`. -/
theorem fderiv_upper_mul_eq_zero {χ : ℕ → ℝˣ → ℂ} {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ n χ) (g : Langlands.GeneralLinear n ℝ) (hg : f g = 0)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) :
    fderiv ℝ (unitsExtension f) (g : Matrix (Fin n) (Fin n) ℝ)
        (U * (g : Matrix (Fin n) (Fin n) ℝ)) = 0 := by
  set Δ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i => U i i with hΔ
  set N : Matrix (Fin n) (Fin n) ℝ := U - Δ with hN
  have hNu : N.IsUpperTriangular := hU.sub (Matrix.blockTriangular_diagonal _)
  have hNd : ∀ i, N i i = 0 := fun i => by simp [hN, hΔ]
  set Γ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t =>
    NormedSpace.exp (t • Δ) * (1 + t • N) * (g : Matrix (Fin n) (Fin n) ℝ) with hΓ
  have hΓd : HasDerivAt Γ (U * (g : Matrix (Fin n) (Fin n) ℝ)) 0 := by
    have h1 := hasDerivAt_exp_smul_zero Δ
    have h2 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + t • N) N 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add 1
    have h3 := (h1.mul h2).mul_const (g : Matrix (Fin n) (Fin n) ℝ)
    have e : (Δ * (1 + (0 : ℝ) • N) + NormedSpace.exp ((0 : ℝ) • Δ) * N) *
        (g : Matrix (Fin n) (Fin n) ℝ) = U * (g : Matrix (Fin n) (Fin n) ℝ) := by
      simp only [zero_smul, add_zero, NormedSpace.exp_zero, one_mul, mul_one]
      rw [hN, add_sub_cancel]
    exact h3.congr_deriv e
  have hΓ0 : Γ 0 = g := by simp [hΓ]
  have hval : ∀ t : ℝ, Γ t = ((matrixExpUnit n (Matrix.diagonal fun i => t * U i i) *
      ((unipotentLine N hNu hNd t : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) * g :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
    intro t
    have hsd : t • Δ = Matrix.diagonal fun i => t * U i i := by
      rw [hΔ, ← Matrix.diagonal_smul]
      rfl
    simp only [Units.val_mul, matrixExpUnit_val, unipotentLine_val, hΓ, hsd]
  have hcomp : (fun t => unitsExtension f (Γ t)) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    rw [hval t, unitsExtension_val, matrixExpUnit_diagonal,
      ((mem_principalSeries_iff ℝ n χ f).mp hf).2, hg, mul_zero]
  have hd1 : HasDerivAt (fun t => unitsExtension f (Γ t))
      (fderiv ℝ (unitsExtension f) (g : Matrix (Fin n) (Fin n) ℝ)
        (U * (g : Matrix (Fin n) (Fin n) ℝ))) 0 := by
    have hdiff : HasFDerivAt (unitsExtension f)
        (fderiv ℝ (unitsExtension f) (g : Matrix (Fin n) (Fin n) ℝ)) (Γ 0) := by
      rw [hΓ0]
      exact (differentiableAt_unitsExtension hf.1 (Units.isUnit g)).hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hΓd
  rw [hcomp] at hd1
  exact hd1.unique (hasDerivAt_const 0 0)

/-- For `f` in the principal series of `GL_n(ℝ)` with `f(1) = 0` and `X` upper triangular,
`(R(X) f)(1) = 0`. -/
theorem rightDerivative_apply_one_eq_zero {χ : ℕ → ℝˣ → ℂ}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n χ) (h1 : f 1 = 0)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsUpperTriangular) :
    rightDerivative (matrixModel ℝ n) X f 1 = 0 := by
  rw [rightDerivative_eq_fderiv hf.1, Units.val_one, one_mul]
  have h := fderiv_upper_mul_eq_zero hf 1 h1 hX
  rwa [Units.val_one, mul_one] at h

/-! ## Evaluation at the identity -/

section KFinite

variable {χ : ℕ → ℝˣ → ℂ} (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
  (hV : ∀ f ∈ V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
  (hVK : ∀ k ∈ unitaryCompact ℝ n, ∀ f ∈ V,
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f ∈ V)
  (hVX : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ f ∈ V, rightDerivative (matrixModel ℝ n) X f ∈ V)

/-- `c ⊗ X` acts on evaluation at `1` by a scalar for every upper triangular `X`. -/
theorem tmul_mem_scalarSubmodule (hVps : V ≤ principalSeries ℝ n χ) (c : ℂ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsUpperTriangular) :
    (c ⊗ₜ[ℝ] X) ∈ scalarSubmodule (kFiniteLie V hV hVK hVX) (kFiniteEval V 1) := by
  have h1 : ((1 : ℂ) ⊗ₜ[ℝ] X) ∈ scalarSubmodule (kFiniteLie V hV hVK hVX) (kFiniteEval V 1) := by
    rw [mem_scalarSubmodule]
    refine ComplexPrincipalSeriesInfChar.exists_eq_smul_of_ker_le fun f hf => ?_
    rw [LinearMap.comp_apply, kFiniteEval_apply, kFiniteLie_one_tmul_apply_coe]
    rw [kFiniteEval_apply] at hf
    exact rightDerivative_apply_one_eq_zero (hVps f.2.1) hf hX
  have hc : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hc]
  exact Submodule.smul_mem _ c h1

/-! ## The lowering elements -/

/-- The weight element `H = 1 ⊗ D`, `D = diag(0, -1, …, -(n-1))`. -/
def weightH : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (1 : ℂ) ⊗ₜ[ℝ] Matrix.diagonal fun p => -((p : ℕ) : ℝ)

/-- The lowering elements `c ⊗ r E_pq` with `q < p`: complex multiples of strictly lower
triangular real matrix units. -/
def lowering : Set (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  {y | ∃ (p q : Fin n) (c : ℂ) (r : ℝ), q < p ∧ y = c ⊗ₜ[ℝ] Matrix.single p q r}

theorem diagonal_mul_sub_mul_diagonal (d : Fin n → ℝ) (p q : Fin n) (r : ℝ) :
    Matrix.diagonal d * Matrix.single p q r - Matrix.single p q r * Matrix.diagonal d =
      (d p - d q) • Matrix.single p q r := by
  ext s t
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · ring

theorem lie_weightH_lowering :
    ∀ y ∈ (lowering : Set (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)),
      ∃ k : ℕ, 0 < k ∧ ⁅(weightH : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ), y⁆ = -((k : ℂ) • y) := by
  rintro y ⟨p, q, c, r, hqp, rfl⟩
  refine ⟨(p : ℕ) - (q : ℕ), Nat.sub_pos_of_lt hqp, ?_⟩
  rw [weightH, LieAlgebra.ExtendScalars.bracket_tmul, one_mul, Ring.lie_def,
    diagonal_mul_sub_mul_diagonal, TensorProduct.tmul_smul,
    Nat.cast_sub (Fin.le_iff_val_le_val.1 hqp.le)]
  rw [← IsScalarTower.algebraMap_smul ℂ]
  rw [← neg_smul]
  congr 1
  simp only [Complex.coe_algebraMap, Complex.ofReal_sub, Complex.ofReal_neg,
    Complex.ofReal_natCast]
  ring

/-- Every element of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` acts on evaluation at `1` by a scalar plus an element of
the span of the lowering elements. -/
theorem decSubmodule_eq_top (hVps : V ≤ principalSeries ℝ n χ) :
    decSubmodule (kFiniteLie V hV hVK hVX) (kFiniteEval V 1) lowering = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul c X =>
    rw [Matrix.matrix_eq_sum_single X, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun p _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    rcases lt_or_ge q p with hqp | hpq
    · exact subset_decSubmodule _ _ _ ⟨p, q, c, _, hqp, rfl⟩
    · refine scalarSubmodule_le_decSubmodule _ _ _
        (tmul_mem_scalarSubmodule V hV hVK hVX hVps c fun i j hji => ?_)
      rw [Matrix.single_apply]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd hpq (not_le.2 hji)
      · rfl

/-! ## The infinitesimal character -/

/-- **The `O(n)`-finite functions of a space of principal-series functions have an
infinitesimal character.** -/
theorem hasInfinitesimalCharacter_kFiniteLie (hVps : V ≤ principalSeries ℝ n χ) :
    HasInfinitesimalCharacter (kFiniteLie V hV hVK hVX) := by
  intro z hz
  obtain ⟨μ, hμ⟩ := tmul_mem_scalarSubmodule V hV hVK hVX hVps 1
      (X := Matrix.diagonal fun p => -((p : ℕ) : ℝ)) (Matrix.blockTriangular_diagonal _)
  have hdec : ∀ x, ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ lowering,
      kFiniteEval V 1 ∘ₗ kFiniteLie V hV hVK hVX x =
        c • kFiniteEval V 1 + kFiniteEval V 1 ∘ₗ kFiniteLie V hV hVK hVX y := fun x =>
    (mem_decSubmodule _ _ _).1 (by rw [decSubmodule_eq_top V hV hVK hVX hVps]; trivial)
  obtain ⟨c, hc⟩ := exists_comp_envelopingAction_eq_smul weightH μ hμ lie_weightH_lowering
    hdec hz
  refine ⟨c, ?_⟩
  set Z := envelopingAction (kFiniteLie V hV hVK hVX) z with hZdef
  have hZρ : ∀ k, kFiniteRep V hVK k * Z = Z * kFiniteRep V hVK k := by
    intro k
    rw [hZdef, rho_mul_envelopingAction (isRealGKModule_kFinite V hV hVK hVX).2.2.2 k z,
      fixesCenter_of_det_ne_zero _ (det_ne_zero_of_orth k) (orthUnit k) (orthUnit_val k) z hz]
  have hev : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (F : kFiniteFunctions V (unitaryCompact ℝ n)),
      kFiniteEval V 1 (kFiniteRep V hVK k F) =
        (F : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) := by
    intro k F
    rw [kFiniteEval_apply, kFiniteRep_apply_coe]
    change (F : Langlands.GeneralLinear n ℝ → ℂ) (1 * Unitary.toUnits k) = _
    rw [one_mul]
  refine LinearMap.ext fun f => ?_
  rw [Module.algebraMap_end_apply]
  apply Subtype.ext
  have hmem : ((Z f : kFiniteFunctions V (unitaryCompact ℝ n)) :
      Langlands.GeneralLinear n ℝ → ℂ) - c • (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        principalSeries ℝ n χ :=
    sub_mem (hVps (Z f).2.1) (Submodule.smul_mem _ c (hVps f.2.1))
  have h0 := eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact hmem fun g hg => by
    let k : Matrix.unitaryGroup (Fin n) ℝ :=
      ⟨((g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), hg⟩
    have hk : (Unitary.toUnits k : Langlands.GeneralLinear n ℝ) = g := Units.ext rfl
    have h1 := hev k (Z f)
    rw [← Module.End.mul_apply, hZρ k, Module.End.mul_apply] at h1
    have h2 := LinearMap.congr_fun hc (kFiniteRep V hVK k f)
    rw [LinearMap.comp_apply, LinearMap.smul_apply, hev k f, hk] at h2
    rw [hk] at h1
    rw [Pi.sub_apply, Pi.smul_apply, ← h1, h2, sub_self]
  rw [Submodule.coe_smul]
  exact sub_eq_zero.1 h0

end KFinite

end RealPrincipalSeriesInfChar

open RealPrincipalSeriesInfChar in
/-- Proof of `RealPrincipalSeriesInfinitesimalCharacterStatement`. -/
theorem realPrincipalSeriesInfinitesimalCharacter :
    RealPrincipalSeriesInfinitesimalCharacterStatement := fun n χ =>
  hasInfinitesimalCharacter_kFiniteLie (principalSeries ℝ n χ) _ _ _ le_rfl

open RealPrincipalSeriesInfChar Langlands.LocalFactor.Archimedean in
/-- Every real standard module has an infinitesimal character. -/
theorem realStandardLie_hasInfinitesimalCharacter (n : ℕ) (ds : List RealBlock) :
    HasInfinitesimalCharacter (realStandardLie n ds) :=
  hasInfinitesimalCharacter_kFiniteLie (realStandardModule n ds) _ _ _
    (realStandardModule_le_principalSeries n ds)

end Langlands.Archimedean
